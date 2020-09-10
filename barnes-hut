structure BarnesHut =
struct

  open Mechanics
  structure BB = BoundingBox
  open Plane
  open TestData

  infixr 3 ++
  infixr 4 **
  infixr 4 //
  infixr 3 -->

  datatype bhtree =
      Empty
    | Single of body
    | Cell of (Scalar.scalar * Plane.point) * BB.bbox * bhtree * bhtree * bhtree * bhtree
      (* ((mass, center), box, top-left, top-right, bottom-left, bottom-right) *)

  (* Projects the mass and center from the root node of a bhtree *)
  fun center_of_mass (T : bhtree) : Scalar.scalar * Plane.point =
      case T of
          Empty => (Scalar.zero, Plane.origin)
        | Single (m, p, _) => (m, p)
        | Cell (com, _, _,_,_,_) => com

  (* Note: Doesn't compare velocities as these are unaffected by compute_tree *)
  fun bodyEq ((m1, p1, _) : body, (m2, p2, _) : body) : bool =
      (Scalar.eq (m1, m2)) andalso Plane.pointEqual (p1, p2)

  fun bhtreeEq (t1 : bhtree, t2 : bhtree) : bool =
      case (t1, t2) of
          (Empty, Empty) => true
        | (Single b1, Single b2) => bodyEq (b1, b2)
        | (Cell ((cm1, cp1), bb1, tl1,tr1,bl1,br1), Cell ((cm2, cp2), bb2, tl2,tr2,bl2,br2)) =>
              Scalar.eq (cm1, cm2) andalso
              Plane.pointEqual (cp1, cp2) andalso
              BB.equal (bb1, bb2) andalso
              bhtreeEq (tl1,tl2) andalso bhtreeEq (tr1,tr2) andalso
              bhtreeEq (bl1,bl2) andalso bhtreeEq (br1,br2)
        | (_, _) => false

  (* ---------------------------------------------------------------------- *)
  (* TASKS *)

  (* TASK *)
  (* Compute the barycenter of four points.
     Assumes that all points have nonnegative mass, and
     that at least one point has strictly positive mass. *)
  fun barycenter ((m1,p1) : (Scalar.scalar * Plane.point),
                  (m2,p2) : (Scalar.scalar * Plane.point),
                  (m3,p3) : (Scalar.scalar * Plane.point),
                  (m4,p4) : (Scalar.scalar * Plane.point)) : Scalar.scalar * Plane.point =
      let
            val m = Scalar.plus(Scalar.plus(Scalar.plus(m1,m2),m3),m4)
            val v1 = Plane.-->(Plane.origin,p1)
            val v2 = Plane.-->(Plane.origin,p2)
            val v3 = Plane.-->(Plane.origin,p3)
            val v4 = Plane.-->(Plane.origin,p4)
            val v_total = Plane.++(Plane.++(Plane.++(Plane.**(v1,m1),Plane.**(v2,m2)),Plane.**(v3,m3)),Plane.**(v4,m4))
            val inverse_m = Scalar.invert(m)
      in
            (m,Plane.head(Plane.**(v_total,inverse_m)))
      end

  fun test_barycenter() =
      let
          val (barymass,baryloc) =
              barycenter ((Scalar.one,p00), (Scalar.one,p02), (Scalar.one,p01), (Scalar.plus(Scalar.one,Scalar.one),p44))
      in
          (testb "bmass" (Scalar.eq(barymass, Scalar.fromInt 5)) true;
           testb "bloc" (Plane.pointEqual(baryloc, Plane.fromcoord(Scalar.fromRatio(8,5), Scalar.fromRatio(11,5)))) true)
      end

  (* TASK *)
  (* Compute the four quadrants of the bounding box *)
  fun quarters (bb : BB.bbox) : BB.bbox * BB.bbox * BB.bbox * BB.bbox =
      let
            val (tl,tr,bl,br) = BB.corners(bb)
            val center = BB.center(bb)
      in
            (BB.from2Points(tl,center),BB.from2Points(tr,center),BB.from2Points(bl,center),BB.from2Points(br,center))
      end

  (* Test for quarters: *)
  fun test_quarters() =
      testb "q1" (let val (tl,tr,bl,br) = quarters(bb4)
                  in BB.equal(tl,bb0) andalso BB.equal(tr,bb1) andalso
                      BB.equal(bl, bb2) andalso BB.equal(br,bb3)
                  end) true

  (* TASK *)
  (* Computes the Barnes-Hut tree for the bodies in the given sequence.
   * Assumes all the bodies are contained in the given bounding box,
     and that no two bodies have collided (or are so close that dividing the
     bounding box will not eventually separate them).
     *)
  fun compute_tree (s : body Seq.seq) (bb : BB.bbox) : bhtree =
      case Seq.length(s) of
            0 => Empty
            |1 => Single(Seq.nth 0 s)
            |_ => let val (tl,tr,bl,br) = quarters(bb)
                      val tl_seq = Seq.filter (fn (m,p,v) => BB.contained (false,false,false,false) (p,tl)) s
                      val tr_seq = Seq.filter(fn (m,p,v) => BB.contained (true,false,false,false) (p,tr)) s
                      val bl_seq = Seq.filter(fn (m,p,v) => BB.contained (false,false,true,false) (p,bl)) s
                      val br_seq = Seq.filter(fn (m,p,v) => BB.contained (true,false,true,false) (p,br)) s
                      val tl_bhtree = compute_tree tl_seq tl
                      val tr_bhtree = compute_tree tr_seq tr
                      val bl_bhtree = compute_tree bl_seq bl
                      val br_bhtree = compute_tree br_seq br
                      val (m1,p1) = center_of_mass(tl_bhtree)
                      val (m2,p2) = center_of_mass(tr_bhtree)
                      val (m3,p3) = center_of_mass(bl_bhtree)
                      val (m4,p4) = center_of_mass(br_bhtree)
                      val (m, c) = barycenter((m1,p1),(m2,p2),(m3,p3),(m4,p4))
                  in
                      Cell ((m, c), bb, tl_bhtree,tr_bhtree,bl_bhtree,br_bhtree)
                  end


  (* Test for compute_tree: *)
  fun test_compute_tree() =
      let
          val three_bodies = Seq.cons body1 (Seq.cons body2 (Seq.cons body3 (Seq.empty())))
          val three_bodies_tree = Cell ((Scalar.fromInt 3, p22), bb4,
                                        Cell ((Scalar.fromInt 2, p13), bb0,
                                              Single body3, Empty, Empty, Single body2),
                                        Empty,
                                        Empty,
                                        Single body1)
      in
          testb "c1" (bhtreeEq (compute_tree three_bodies bb4, three_bodies_tree)) true
      end

  (* TASK *)
  (* too_far p1 p2 bb t determines if point p1 is "too far" from
   * a region bb with barycenter p2, given a threshold parameter t,
   * for it to be worth recuring into the region
   *)
  fun too_far (p1 : Plane.point) (p2 : Plane.point) (bb : BB.bbox) (t : Scalar.scalar) : bool =
      let
          val diam = BB.diameter(bb)
          val dist = Plane.distance p1 p2
      in
          Scalar.compare(Scalar.divide(diam,dist),t) = LESS orelse Scalar.compare(Scalar.divide(diam,dist),t) = EQUAL
      end


  (* TASK *)
  (* Computes the acceleration on b from the tree T using the Barnes-Hut
   * algorithm with threshold t
   *)
  fun bh_acceleration (T : bhtree) (t : Scalar.scalar) (b : body) : Plane.vec =
      let val (m,p,v) = b
      in
          case T of
                Empty => Plane.zero
                |Single(single_b) => Mechanics.accOn(b,single_b)
                |Cell((m, c), bb, tl_bhtree,tr_bhtree,bl_bhtree,br_bhtree) =>
                    case (too_far p c bb t) of
                        true => Mechanics.accOnPoint(p, (m,c))
                        |false => Plane.++(Plane.++(Plane.++((bh_acceleration tl_bhtree t b),(bh_acceleration tr_bhtree t b)),
                                  (bh_acceleration bl_bhtree t b)),(bh_acceleration br_bhtree t b))
      end


  (* TASK
     Given a threshold and a sequence of bodies, compute the acceleration
     on each body using the Barnes-Hut algorithm.
   *)
  fun barnes_hut (threshold : Scalar.scalar) (s : body Seq.seq) : Plane.vec Seq.seq =
      let val point_seq = Seq.map (fn (m,p,v) => p) s
          val bb = BB.fromPoints(point_seq)
          val bh_tree = compute_tree s bb
      in
          Seq.map (fn body => bh_acceleration bh_tree threshold body) s
      end

  (* Default value of the threshold, theta = 0.5 *)
  val threshold = (Scalar.fromRatio (1,2))

  val accelerations : body Seq.seq -> Plane.vec Seq.seq = barnes_hut threshold

end
