-- Prove2me | solution 1 for Esgk.general_position_seven_le_five
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T02:27:11.861833+00:00
-- url     : https://prove2.me/submissions/aac64fcf-5779-4ce4-a7ec-d35552c0e238

import Definitions.Def_Esgk_Foundation

open EuclideanGeometry
open scoped EuclideanGeometry

namespace Esgk

set_option maxHeartbeats 0

private def xy (a b : ℝ) : Point :=
  WithLp.toLp 2 ![a, b]

@[simp] private theorem xy_zero (a b : ℝ) : xy a b 0 = a := rfl
@[simp] private theorem xy_one (a b : ℝ) : xy a b 1 = b := rfl

private theorem dist_sq_xy (a b : Point) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private def area (o a b : Point) : ℝ :=
  (a 0 - o 0) * (b 1 - o 1) - (a 1 - o 1) * (b 0 - o 0)

private noncomputable def liftedArea (o a b c : Point) : ℝ :=
  area o a b * dist c o ^ 2 - area o a c * dist b o ^ 2
    + area o b c * dist a o ^ 2

private theorem area_zero_of_collinear {o a b : Point}
    (h : Collinear ℝ ({o, a, b} : Set Point)) : area o a b = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := o) (by simp : o ∈ ({o,a,b} : Set Point))).mp h
  obtain ⟨s, hs⟩ := hv a (by simp)
  obtain ⟨t, ht⟩ := hv b (by simp)
  have ha (i : Fin 2) : a i = s * v i + o i := by
    simpa using congrFun (congrArg WithLp.ofLp hs) i
  have hb (i : Fin 2) : b i = t * v i + o i := by
    simpa using congrFun (congrArg WithLp.ofLp ht) i
  unfold area
  rw [ha 0, ha 1, hb 0, hb 1]
  ring

private theorem liftedArea_zero_of_dist_eq {o a b c center : Point} (radius : ℝ)
    (ho : dist o center = radius) (ha : dist a center = radius)
    (hb : dist b center = radius) (hc : dist c center = radius) :
    liftedArea o a b c = 0 := by
  have same (p : Point) (h : dist p center = radius) :
      dist p o ^ 2 = 2 * ((p 0 - o 0) * (center 0 - o 0) + (p 1 - o 1) * (center 1 - o 1)) := by
    have eq : dist p center ^ 2 = dist o center ^ 2 := by rw [h, ho]
    rw [dist_sq_xy, dist_sq_xy] at eq
    rw [dist_sq_xy]
    linarith only [eq]
  unfold liftedArea
  rw [same a ha, same b hb, same c hc]
  unfold area
  ring


private theorem image_contains {n : ℕ} (p : Config n) (i : Fin n) :
    p i ∈ Config.toFinset p := by
  classical
  simp [Config.toFinset, Finset.mem_image]

private theorem gp_of_area {n : ℕ} (p : Config n) (hp : Function.Injective p)
    (htri : ∀ i j k : Fin n, i < j → j < k → area (p i) (p j) (p k) ≠ 0)
    (hquad : ∀ i j k l : Fin n, i < j → j < k → k < l →
      liftedArea (p i) (p j) (p k) (p l) ≠ 0) :
    InGeneralPosition (p.toFinset) := by
  classical
  constructor
  · intro o ho a ha b hb hoa hab hob hcol
    have preimage (q : Point) (hq : q ∈ (p.toFinset : Set Point)) :
        ∃ i, p i = q := by simpa [Config.toFinset, Finset.mem_image] using hq
    obtain ⟨i, rfl⟩ := preimage o ho
    obtain ⟨j, rfl⟩ := preimage a ha
    obtain ⟨k, rfl⟩ := preimage b hb
    let T : Finset (Fin n) := {i,j,k}
    have hcard : T.card = 3 := by
      refine Finset.card_eq_three.mpr ⟨i,j,k,?_,?_,?_,rfl⟩
      all_goals solve | exact fun h => hoa (congrArg p h) | exact fun h => hob (congrArg p h) | exact fun h => hab (congrArg p h)
    let e := T.orderEmbOfFin hcard
    have point_mem (u : Fin 3) : p (e u) ∈ ({p i,p j,p k} : Set Point) := by
      have hu : e u ∈ T := T.orderEmbOfFin_mem hcard u
      simp [T] at hu
      rcases hu with h | h | h <;> simp [h]
    apply htri (e 0) (e 1) (e 2) (e.strictMono (by decide)) (e.strictMono (by decide))
    refine area_zero_of_collinear (hcol.subset ?_)
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact point_mem 0
    · exact point_mem 1
    · exact point_mem 2
  · intro T hT hc hcos
    let U := Finset.univ.filter (fun i : Fin n ↦ p i ∈ T)
    have hmem (i : Fin n) : i ∈ U ↔ p i ∈ T := by simp [U]
    have him : U.image p = T := by
      ext q
      constructor
      · intro hq
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
        exact (hmem i).mp hi
      · intro hq
        have hq' : q ∈ p.toFinset := hT hq
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq'
        exact Finset.mem_image.mpr ⟨i,(hmem i).mpr hq,rfl⟩
    have hcU : U.card = 4 := by
      rw [← Finset.card_image_of_injective U hp, him, hc]
    let e := U.orderEmbOfFin hcU
    obtain ⟨center, radius, hd⟩ := hcos
    have at_radius (u : Fin 4) : dist (p (e u)) center = radius :=
      hd _ ((hmem (e u)).mp (U.orderEmbOfFin_mem hcU u))
    exact hquad (e 0) (e 1) (e 2) (e 3) (e.strictMono (by decide))
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (liftedArea_zero_of_dist_eq radius (at_radius 0) (at_radius 1) (at_radius 2) (at_radius 3))


set_option maxRecDepth 16384
private noncomputable def distanceValues {n : ℕ} (p : Config n) : Finset ℝ := by
  classical
  exact p.toFinset.offDiag.image (fun v : Point × Point => dist v.1 v.2)

private theorem point_distance_mem {n : ℕ} (p : Config n) (hp : Function.Injective p)
    (i j : Fin n) (hij : i ≠ j) : dist (p i) (p j) ∈ distanceValues p := by
  classical
  exact Finset.mem_image.mpr ⟨(p i,p j), Finset.mem_offDiag.mpr
    ⟨image_contains p i,image_contains p j, fun h => hij (hp h)⟩, rfl⟩

private theorem distance_indices {n : ℕ} (p : Config n) {d : ℝ}
    (hd : d ∈ distanceValues p) :
    ∃ i j : Fin n, i ≠ j ∧ dist (p i) (p j) = d := by
  classical
  obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
  exact ⟨i,j,fun h => hne (congrArg p h),rfl⟩

private theorem positive_distance {n : ℕ} (p : Config n) (hp : Function.Injective p)
    {d : ℝ} (hd : d ∈ distanceValues p) : 0 < d := by
  obtain ⟨i,j,hne,rfl⟩ := distance_indices p hd
  exact dist_pos.mpr (fun h => hne (hp h))


private abbrev LatticePoint := ℤ × ℤ

private def latticeDiff (x y : LatticePoint) : LatticePoint := (x.1-y.1,x.2-y.2)

private def triangleInt (o a b : LatticePoint) : ℤ :=
  (a.1-o.1)*(b.2-o.2)-(a.2-o.2)*(b.1-o.1)

private def normInt (p : LatticePoint) : ℤ := p.1^2+p.1*p.2+p.2^2

private def circleInt (o a b c : LatticePoint) :=
  triangleInt o a b * normInt (latticeDiff c o) -
  triangleInt o a c * normInt (latticeDiff b o) +
  triangleInt o b c * normInt (latticeDiff a o)

private noncomputable def toPlane (s : ℝ) (p : LatticePoint) : Point :=
  xy ((p.1 : ℝ) + (p.2 : ℝ)/2) (s*(p.2 : ℝ)/2)

private theorem toPlane_inj (s : ℝ) (hs : s ≠ 0) : Function.Injective (toPlane s) := by
  intro a b h
  have hx := congrArg (fun p : Point => p 0) h
  have hy := congrArg (fun p : Point => p 1) h
  simp only [toPlane,xy_zero] at hx
  simp only [toPlane,xy_one] at hy
  have he : s*(((a.2 : ℝ)-(b.2 : ℝ))) = 0 := by linarith only [hy]
  have hy' : (a.2 : ℝ) = (b.2 : ℝ) := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)
  have hx' : (a.1 : ℝ) = (b.1 : ℝ) := by linarith only [hx,hy']
  exact Prod.ext (by exact_mod_cast hx') (by exact_mod_cast hy')

private theorem distance_lattice (s : ℝ) (hs : s^2=3) (x y : LatticePoint) :
    dist (toPlane s x) (toPlane s y)^2 = (normInt (latticeDiff x y) : ℝ) := by
  rw [dist_sq_xy]
  simp only [toPlane,xy_zero,xy_one,normInt,latticeDiff]
  push_cast
  linear_combination (((x.2 : ℝ)-(y.2 : ℝ))^2 / 4)*hs

private theorem triangle_lattice (s : ℝ) (o a b : LatticePoint) :
    area (toPlane s o) (toPlane s a) (toPlane s b) =
      s/2 * (triangleInt o a b : ℝ) := by
  simp only [area,toPlane,xy_zero,xy_one,triangleInt]
  push_cast
  ring

private theorem circle_lattice (s : ℝ) (hs : s^2=3) (o a b c : LatticePoint) :
    liftedArea (toPlane s o) (toPlane s a) (toPlane s b) (toPlane s c) =
      s/2 * (circleInt o a b c : ℝ) := by
  simp only [liftedArea,triangle_lattice,distance_lattice s hs,circleInt]
  push_cast
  ring

private theorem lattice_upper {n : ℕ} (v : Fin n → LatticePoint)
    (hv : Function.Injective v) (allowed : Finset ℤ)
    (ht : ∀ i j k : Fin n, i < j → j < k → triangleInt (v i) (v j) (v k) ≠ 0)
    (hq : ∀ i j k l : Fin n, i < j → j < k → k < l →
      circleInt (v i) (v j) (v k) (v l) ≠ 0)
    (hd : ∀ i j : Fin n, i ≠ j → normInt (latticeDiff (v i) (v j)) ∈ allowed) :
    ∃ p : Config n, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
      distinctDistances p.toFinset ≤ allowed.card := by
  classical
  let s := Real.sqrt 3
  have hs : s^2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : s ≠ 0 := (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<3)).ne'
  let p := toPlane s ∘ v
  have hi := (toPlane_inj s h0).comp hv
  have hT (i j k : Fin n) (hij : i<j) (hjk : j<k) : area (p i) (p j) (p k) ≠ 0 := by
    change area (toPlane s (v i)) (toPlane s (v j)) (toPlane s (v k)) ≠ 0
    rw [triangle_lattice]
    exact mul_ne_zero (div_ne_zero h0 (by norm_num)) (by exact_mod_cast ht i j k hij hjk)
  have hQ (i j k l : Fin n) (hij : i<j) (hjk : j<k) (hkl : k<l) :
      liftedArea (p i) (p j) (p k) (p l) ≠ 0 := by
    change liftedArea (toPlane s (v i)) (toPlane s (v j)) (toPlane s (v k)) (toPlane s (v l)) ≠ 0
    rw [circle_lattice s hs]
    exact mul_ne_zero (div_ne_zero h0 (by norm_num)) (by exact_mod_cast hq i j k l hij hjk hkl)
  refine ⟨p,hi,gp_of_area p hi hT hQ,?_⟩
  let imageR := allowed.image (fun u : ℤ => Real.sqrt (u : ℝ))
  have hsub : distanceValues p ⊆ imageR := by
    intro q hq
    obtain ⟨i,j,hij,rfl⟩ := distance_indices p hq
    refine Finset.mem_image.mpr ⟨normInt (latticeDiff (v i) (v j)), hd i j hij, ?_⟩
    rw [← distance_lattice s hs, Real.sqrt_sq dist_nonneg]
    rfl
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

private def latticeSevenPoints : Fin 7 → LatticePoint :=
  ![(0,0),(-1,1),(2,-3),(4,-2),(2,-4),(3,-1),(4,-1)]

private theorem lattice_seven_bound :
    ∃ p : Config 7, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
      distinctDistances p.toFinset ≤ 5 := by
  let points := latticeSevenPoints
  let distances : Finset ℤ := {1,7,12,13,19}
  have hi : ∀ i j, points i = points j → i=j := by
    dsimp [points]
    decide +kernel
  have ht : ∀ i j k, i < j → j < k → triangleInt (points i) (points j) (points k) ≠ 0 := by
    dsimp [points]
    decide +kernel
  have hq : ∀ i j k l, i<j → j<k → k<l →
      circleInt (points i) (points j) (points k) (points l) ≠ 0 := by
    dsimp [points]
    decide +kernel
  have hd : ∀ i j, i≠j → normInt (latticeDiff (points i) (points j)) ∈ distances := by
    dsimp [points,distances]
    decide +kernel
  have bound : distances.card = 5 := by decide
  simpa only [bound] using lattice_upper points (fun i j h => hi i j h) distances ht hq hd


end Esgk

open Esgk in
theorem solution :
    ∃ p : Config 7, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
      distinctDistances p.toFinset ≤ 5 :=
  Esgk.lattice_seven_bound

#print axioms solution
