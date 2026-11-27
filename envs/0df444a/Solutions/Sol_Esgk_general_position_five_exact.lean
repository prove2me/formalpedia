-- Prove2me | solution 1 for Esgk.general_position_five_exact
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T02:23:46.527715+00:00
-- url     : https://prove2.me/submissions/37fd07ef-b68b-4ced-a9e9-21b5e8905c21

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

private noncomputable def five (s : ℝ) : Config 5 :=
  ![xy 0 0, xy 1 0, xy (1/2) (s/2), xy (-s/2) (-1/2), xy 1 (-1)]

private theorem five_inj (s : ℝ) (hs : 1 < s) :
    Function.Injective (five s) := by
  intro i j h
  have hx := congrArg (fun p : Point ↦ p 0) h
  have hy := congrArg (fun p : Point ↦ p 1) h
  fin_cases i <;> fin_cases j <;> simp [five] at hx hy ⊢ <;> linarith

private theorem five_triangle (s : ℝ) (hs : s ^ 2 = 3) (h1 : 1 < s) (h2 : s < 2)
    (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
    area (five s i) (five s j) (five s k) ≠ 0 := by
  have hcases : (i = 0 ∧ j = 1 ∧ k = 2) ∨
      (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 1 ∧ k = 4) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 4) ∨
      (i = 0 ∧ j = 3 ∧ k = 4) ∨
      (i = 1 ∧ j = 2 ∧ k = 3) ∨
      (i = 1 ∧ j = 2 ∧ k = 4) ∨
      (i = 1 ∧ j = 3 ∧ k = 4) ∨
      (i = 2 ∧ j = 3 ∧ k = 4) := by omega
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp [five, area]
  all_goals intro h; nlinarith only [hs, h1, h2, h]

private theorem five_circle (s : ℝ) (hs : s ^ 2 = 3) (h1 : 1 < s) (h2 : s < 2)
    (i j k l : Fin 5) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    liftedArea (five s i) (five s j) (five s k) (five s l) ≠ 0 := by
  have hcases : (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 3) ∨
      (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 4) ∨
      (i = 0 ∧ j = 1 ∧ k = 3 ∧ l = 4) ∨
      (i = 0 ∧ j = 2 ∧ k = 3 ∧ l = 4) ∨
      (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 4) := by omega
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals simp [five, liftedArea, area, dist_sq_xy]
  all_goals intro h
  all_goals
    have h3 : s ^ 3 = 3 * s := by linear_combination s * hs
    have h4 : s ^ 4 = 9 := by linear_combination (s^2+3) * hs
    nlinarith only [hs, h3, h4, h1, h2, h]

private theorem five_dist (s : ℝ) (hs : s ^ 2 = 3) (i j : Fin 5) (hij : i ≠ j) :
    dist (five s i) (five s j) ^ 2 = 1 ∨
    dist (five s i) (five s j) ^ 2 = 2 ∨
    dist (five s i) (five s j) ^ 2 = 2 + s := by
  rw [dist_sq_xy]
  fin_cases i <;> fin_cases j <;> simp_all [five]
  all_goals first
    | left; nlinarith only [hs]
    | right; left; nlinarith only [hs]
    | right; right; nlinarith only [hs]

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

private theorem five_dist_eq (s : ℝ) (hs : s^2 = 3) :
    dist (five s 0) (five s 1) = 1 ∧
    dist (five s 0) (five s 4) = Real.sqrt 2 ∧
    dist (five s 1) (five s 3) = Real.sqrt (2+s) := by
  have h1 : dist (five s 0) (five s 1) ^ 2 = 1 := by
    rw [dist_sq_xy]
    norm_num [five]
  have h2 : dist (five s 0) (five s 4) ^ 2 = 2 := by
    rw [dist_sq_xy]
    change (0 - 1 : ℝ)^2 + (0 - (-1) : ℝ)^2 = 2
    norm_num
  have h3 : dist (five s 1) (five s 3) ^ 2 = 2+s := by
    rw [dist_sq_xy]
    simp [five]
    nlinarith only [hs]
  rw [← Real.sqrt_sq dist_nonneg, h1, Real.sqrt_one,
    ← Real.sqrt_sq (x := dist (five s 0) (five s 4)) dist_nonneg, h2,
    ← Real.sqrt_sq (x := dist (five s 1) (five s 3)) dist_nonneg, h3]
  exact ⟨rfl,rfl,rfl⟩

private theorem five_witness :
    ∃ p : Config 5, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
      distinctDistances p.toFinset = 3 := by
  classical
  let s := Real.sqrt 3
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h1 : 1 < s := by nlinarith only [hs,hs0]
  have h2 : s < 2 := by nlinarith only [hs]
  let p := five s
  have pinj := five_inj s h1
  refine ⟨p, pinj, gp_of_area p pinj (five_triangle s hs h1 h2) (five_circle s hs h1 h2), ?_⟩
  let d := p.toFinset.offDiag.image (fun pair : Point × Point => dist pair.1 pair.2)
  have hset : d = {1, Real.sqrt 2, Real.sqrt (2+s)} := by
    ext r
    constructor
    · intro hr
      obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      have hij : i ≠ j := fun h => hne (congrArg p h)
      have hd := five_dist s hs i j hij
      rw [← Real.sqrt_sq (x := dist (p i) (p j)) dist_nonneg]
      rcases hd with hd | hd | hd
      · rw [hd, Real.sqrt_one]; simp
      · rw [hd]; simp
      · rw [hd]; simp
    · intro hr
      have mem_dist (i j : Fin 5) (hij : i ≠ j) : dist (p i) (p j) ∈ d :=
        Finset.mem_image.mpr ⟨(p i, p j), Finset.mem_offDiag.mpr
          ⟨image_contains p i, image_contains p j, fun h => hij (pinj h)⟩, rfl⟩
      obtain ⟨h01,h04,h13⟩ := five_dist_eq s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← h01]; exact mem_dist 0 1 (by decide)
      · rw [← h04]; exact mem_dist 0 4 (by decide)
      · rw [← h13]; exact mem_dist 1 3 (by decide)
  have hab : (1 : ℝ) < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (x := 2) (by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [hsq, hn]
  have hbc : Real.sqrt 2 < Real.sqrt (2+s) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  change d.card = 3
  rw [hset]
  exact Finset.card_eq_three.mpr ⟨_, _, _, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩


set_option maxRecDepth 16384

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 0

private def squaredGram (d : Fin 5 → Fin 5 → ℝ) (o i j : Fin 5) : ℝ :=
  d o i + d o j - d i j

private def trianglePolynomial (a b c : ℝ) : ℝ := 4 * a * b - (a + b - c)^2

private def circlePolynomial (a b c d e f : ℝ) : ℝ :=
  (a*f)^2 + (b*e)^2 + (c*d)^2 - 2*(a*f*b*e + b*e*c*d + c*d*a*f)

private structure StandardDistanceData (d : Fin 5 → Fin 5 → ℝ) : Prop where
  gram : ∀ o i j k l,
    (squaredGram d o i i * squaredGram d o j j - (squaredGram d o i j)^2) *
      squaredGram d o k l -
    squaredGram d o j j * squaredGram d o i k * squaredGram d o i l +
    squaredGram d o i j * (squaredGram d o j k * squaredGram d o i l +
      squaredGram d o i k * squaredGram d o j l) -
    squaredGram d o i i * squaredGram d o j k * squaredGram d o j l = 0
  triangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    trianglePolynomial (d i j) (d i k) (d j k) ≠ 0
  circle : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    circlePolynomial (d i j) (d i k) (d i l) (d j k) (d j l) (d k l) ≠ 0

private def edgeIndex (i j : Fin 5) : Fin 10 :=
  ![![0,0,1,2,3], ![0,0,4,5,6], ![1,4,0,7,8], ![2,5,7,0,9], ![3,6,8,9,0]] i j

private def fromColor (c : Fin 10 → Bool) (s a : ℝ) (i j : Fin 5) : ℝ :=
  if i = j then 0 else if c (edgeIndex i j) then a else s


private def twoPatterns : Fin 34 → Fin 10 → Bool := ![
  ![false, false, false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false, false, true],
  ![false, false, false, false, false, false, false, false, true, true],
  ![false, false, false, false, false, false, false, true, true, true],
  ![false, false, false, false, false, false, true, false, true, true],
  ![false, false, false, false, false, false, true, true, false, false],
  ![false, false, false, false, false, false, true, true, false, true],
  ![false, false, false, false, false, false, true, true, true, true],
  ![false, false, false, false, false, true, true, true, true, false],
  ![false, false, false, false, false, true, true, true, true, true],
  ![false, false, false, false, true, true, true, true, true, true],
  ![false, false, false, true, false, false, true, false, true, true],
  ![false, false, false, true, false, false, true, true, false, false],
  ![false, false, false, true, false, false, true, true, false, true],
  ![false, false, false, true, false, false, true, true, true, true],
  ![false, false, false, true, false, true, false, true, true, false],
  ![false, false, false, true, false, true, false, true, true, true],
  ![false, false, false, true, false, true, true, true, true, false],
  ![false, false, false, true, false, true, true, true, true, true],
  ![false, false, false, true, true, true, false, true, false, false],
  ![false, false, false, true, true, true, false, true, false, true],
  ![false, false, false, true, true, true, false, true, true, true],
  ![false, false, false, true, true, true, true, true, true, true],
  ![false, false, true, true, false, true, true, true, true, false],
  ![false, false, true, true, false, true, true, true, true, true],
  ![false, false, true, true, true, false, true, false, true, true],
  ![false, false, true, true, true, false, true, true, false, false],
  ![false, false, true, true, true, false, true, true, false, true],
  ![false, false, true, true, true, false, true, true, true, true],
  ![false, false, true, true, true, true, true, true, true, false],
  ![false, false, true, true, true, true, true, true, true, true],
  ![false, true, true, true, true, true, true, false, true, true],
  ![false, true, true, true, true, true, true, true, true, true],
  ![true, true, true, true, true, true, true, true, true, true]]

private theorem twoCase0 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 0) 1 a)) : False := by
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/4) * e2
  exact one_ne_zero hz

private theorem twoCase1 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 1) 1 a)) : False := by
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/4) * e2
  exact one_ne_zero hz

private theorem twoCase2 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 2) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/4) * e0
  exact one_ne_zero hz

private theorem twoCase3 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 3) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t3 := rd.triangle 0 2 3 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t3
  have gt3 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t3
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (4/3 - a/3) * e0 + (a/3 - 4/3) * e1
  exact gt3 hz

private theorem twoCase4 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 4) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/4) * e0
  exact one_ne_zero hz

private theorem twoCase5 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 5) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t2 := rd.triangle 0 1 4 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t2
  have gt2 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t2
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (2/3 - a/6) * e0 + (4/3 - a/3) * e1
  exact gt2 hz

private theorem twoCase6 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 6) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/6) * e0 + (1/3) * e1
  exact one_ne_zero hz

private theorem twoCase7 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 7) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1 e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (2 - a/2) * e0 + (a - 4) * e1 + (-1/2) * e2
  exact one_ne_zero hz

private theorem twoCase8 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 8) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/3) * e0 + (-1/3) * e1
  exact one_ne_zero hz

private theorem twoCase9 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 9) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (5/6 - a/3) * e0 + (a/3 - 4/3) * e1
  exact one_ne_zero hz

private theorem twoCase10 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 10) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t6 := rd.triangle 1 2 3 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t6
  have gt6 : (3*a^2 : ℝ) ≠ 0 := by
    intro hz
    apply t6
    linear_combination hz
  have hz : ((3*a^2) : ℝ) = 0 := by
    linear_combination (3/2) * e0 + (-3) * e1
  exact gt6 hz

private theorem twoCase11 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 11) 1 a)) : False := by
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1) * e1
  exact one_ne_zero hz

private theorem twoCase12 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 12) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1 e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (4/5 - a/5) * e0 + (4/5 - a/5) * e1 + (-1/2) * e2
  exact one_ne_zero hz

private theorem twoCase13 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 13) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (7/27 - 2*a/27) * e0 + (1/3 - 2*a/27) * e1
  exact one_ne_zero hz

private theorem twoCase14 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 14) 1 a)) : False := by
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e1 e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (3) * e1 + (-1/2) * e2
  exact one_ne_zero hz

private theorem twoCase15 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 15) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (a/9 + 5/18) * e0 + (2*a/9 - 7/9) * e1
  exact one_ne_zero hz

private theorem twoCase16 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 16) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/6 - a/6) * e0 + (4/3 - a/3) * e1
  exact one_ne_zero hz

private theorem twoCase17 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 17) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (25/78) * e0 + (5*a/39 - 16/39) * e1
  exact one_ne_zero hz

private theorem twoCase18 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 18) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (2/3) * e0 + (2*a/3 - 7/3) * e1
  exact one_ne_zero hz

private theorem twoCase19 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 19) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t6 := rd.triangle 1 2 3 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t6
  have gt6 : (3*a^2 : ℝ) ≠ 0 := by
    intro hz
    apply t6
    linear_combination hz
  have hz : ((3*a^2) : ℝ) = 0 := by
    linear_combination (1/2) * e0 + (1) * e1
  exact gt6 hz

private theorem twoCase20 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 20) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t0 := rd.triangle 0 1 2 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t0
  have gt0 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t0
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (a^2/28 - 3*a/8 + 13/14) * e0 + (a^2/28 - 11*a/28 + 1) * e1
  exact gt0 hz

private theorem twoCase21 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 21) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1 e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (a^3/20 - 3*a^2/10 + 3*a/10 + 2/5) * e0 + (a^3/10 - 7*a^2/10 + 4*a/5 + 1) * e1 + (-1/2) * e2
  exact one_ne_zero hz

private theorem twoCase22 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 22) 1 a)) : False := by
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e1 e2
  have t0 := rd.triangle 0 1 2 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t0
  have gt0 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t0
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (a^2 - 8*a + 16) * e1 + (a/2 - 2) * e2
  exact gt0 hz

private theorem twoCase23 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 23) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/3) * e0 + (-1/3) * e1
  exact one_ne_zero hz

private theorem twoCase24 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 24) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (1/2) * e0 + (-1) * e1
  exact one_ne_zero hz

private theorem twoCase25 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 25) 1 a)) : False := by
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e1 e2
  have t0 := rd.triangle 0 1 2 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t0
  have gt0 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t0
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (2*a^2/3 - 5*a + 28/3) * e1 + (-a^2/3 + 11*a/6 - 2) * e2
  exact gt0 hz

private theorem twoCase26 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 26) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have q0 := rd.circle 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, circlePolynomial] at q0
  have gq0 : (a^4 - 2*a^3 - a^2 - 2*a + 1 : ℝ) ≠ 0 := by
    intro hz
    apply q0
    linear_combination hz
  have hz : ((a^4 - 2*a^3 - a^2 - 2*a + 1) : ℝ) = 0 := by
    linear_combination (-3*a^2/10 - 3*a/10 - 3/10) * e0 + (a^2/5 + a/5 + 1/5) * e1
  exact gq0 hz

private theorem twoCase27 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 27) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have hz : (1 : ℝ) = 0 := by
    linear_combination (29*a^2/75 - 71*a/75 + 77/150) * e0 + (-29*a^2/75 + 14*a/25 + 76/75) * e1
  exact one_ne_zero hz

private theorem twoCase28 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 28) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1 e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (3*a^2/2 - 11*a/2 - 1/2) * e0 + (-3*a^2 + 11*a + 1) * e1 + (4 - 3*a/2) * e2
  exact one_ne_zero hz

private theorem twoCase29 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 29) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t0 := rd.triangle 0 1 2 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t0
  have gt0 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t0
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (-a^2 + 9*a/2 - 2) * e0 + (a^2 - 4*a) * e1
  exact gt0 hz

private theorem twoCase30 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 30) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t0 := rd.triangle 0 1 2 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t0
  have gt0 : (-a^2 + 4*a : ℝ) ≠ 0 := by
    intro hz
    apply t0
    linear_combination hz
  have hz : ((-a^2 + 4*a) : ℝ) = 0 := by
    linear_combination (2 - a/2) * e0 + (a - 4) * e1
  exact gt0 hz

private theorem twoCase31 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 31) 1 a)) : False := by
  have e1 := rd.gram 0 1 2 3 4
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e1 e2
  have hz : (1 : ℝ) = 0 := by
    linear_combination (-6*a - 1) * e1 + (2) * e2
  exact one_ne_zero hz

private theorem twoCase32 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 32) 1 a)) : False := by
  have e0 := rd.gram 0 1 2 3 3
  have e1 := rd.gram 0 1 2 3 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e0 e1
  have t3 := rd.triangle 0 2 3 (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, trianglePolynomial] at t3
  have gt3 : (3*a^2 : ℝ) ≠ 0 := by
    intro hz
    apply t3
    linear_combination hz
  have hz : ((3*a^2) : ℝ) = 0 := by
    linear_combination (3*a) * e0 + (-9*a) * e1
  exact gt3 hz

private theorem twoCase33 (a : ℝ) (ha : 1 < a)
    (rd : StandardDistanceData (fromColor (twoPatterns 33) 1 a)) : False := by
  have e2 := rd.gram 0 1 2 4 4
  simp (config := { decide := true }) [twoPatterns, fromColor, squaredGram, edgeIndex] at e2
  have q0 := rd.circle 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp (config := { decide := true }) [twoPatterns, fromColor, edgeIndex, circlePolynomial] at q0
  have gq0 : (-3*a^4 : ℝ) ≠ 0 := by
    intro hz
    apply q0
    linear_combination hz
  have hz : ((-3*a^4) : ℝ) = 0 := by
    linear_combination (-3*a/4) * e2
  exact gq0 hz

private def permutationCodes : Array Nat := #[2930, 2430, 2830, 1830, 2230, 1730, 2910, 2410, 2710, 1210, 2110, 1110, 2790, 1790, 2690, 1190, 1490, 990, 2170, 1670, 2070, 1070, 1470, 970, 2926, 2426, 2826, 1826, 2226, 1726, 2886, 2386, 2586, 586, 1986, 486, 2766, 1766, 2566, 566, 1366, 366, 2146, 1646, 1946, 446, 1346, 346, 2902, 2402, 2702, 1202, 2102, 1102, 2882, 2382, 2582, 582, 1982, 482, 2642, 1142, 2542, 542, 742, 242, 2022, 1022, 1922, 422, 722, 222, 2778, 1778, 2678, 1178, 1478, 978, 2758, 1758, 2558, 558, 1358, 358, 2638, 1138, 2538, 538, 738, 238, 1398, 898, 1298, 298, 698, 198, 2154, 1654, 2054, 1054, 1454, 954, 2134, 1634, 1934, 434, 1334, 334, 2014, 1014, 1914, 414, 714, 214, 1394, 894, 1294, 294, 694, 194]

private def caseWitnesses : Array (Array Nat) := #[
  #[0, 184, 160, 333, 154, 309, 285, 585, 152, 303, 279, 561, 273, 537, 513, 1353, 136, 331, 330, 450, 696, 832, 826, 957, 672, 808, 802, 933, 1533, 1655, 1653, 1773],
  #[130, 307, 697, 833, 306, 426, 824, 951, 648, 784, 1509, 1631, 778, 909, 1629, 1749, 261, 579, 820, 955, 818, 949, 1056, 1192, 1501, 1624, 1894, 2014, 1870, 1990, 2153, 2273],
  #[128, 301, 673, 809, 649, 785, 1503, 1625, 300, 420, 800, 927, 776, 903, 1623, 1743, 255, 555, 796, 931, 1507, 1630, 1895, 2015, 794, 925, 1032, 1168, 1864, 1984, 2129, 2249],
  #[249, 531, 1531, 1654, 772, 907, 1871, 1991, 770, 901, 1865, 1985, 1008, 1144, 2105, 2225, 489, 1329, 1651, 1771, 1627, 1747, 2152, 2272, 1621, 1741, 2128, 2248, 2104, 2224, 2824, 2944],
  #[124, 699, 283, 827, 282, 825, 402, 945, 624, 1485, 760, 1607, 754, 1605, 885, 1725, 259, 821, 577, 954, 816, 1058, 943, 1186, 1477, 1892, 1600, 2012, 1846, 2147, 1966, 2267],
  #[258, 819, 817, 1060, 576, 948, 942, 1184, 1471, 1868, 1844, 2145, 1594, 1988, 1964, 2265, 378, 939, 937, 1180, 936, 1178, 1176, 1296, 2280, 2513, 2507, 2637, 2505, 2631, 2625, 2745],
  #[600, 1461, 1453, 1890, 1447, 1866, 2304, 2512, 1440, 2329, 1836, 2482, 1830, 2458, 2432, 3033, 736, 1583, 1576, 2010, 1820, 2139, 2501, 2635, 1812, 2476, 2113, 2610, 3120, 3352, 3322, 3453],
  #[730, 1581, 1822, 2141, 1570, 1986, 2499, 2629, 1806, 2452, 3122, 3353, 2089, 2586, 3298, 3429, 861, 1701, 1942, 2261, 1940, 2259, 2619, 2739, 2408, 3009, 3316, 3451, 3292, 3427, 3592, 3712],
  #[122, 675, 277, 803, 625, 1479, 761, 1601, 276, 801, 396, 921, 752, 1599, 879, 1719, 253, 797, 553, 930, 1483, 1893, 1606, 2013, 792, 1034, 919, 1162, 1840, 2123, 1960, 2243],
  #[601, 1455, 1459, 1891, 1441, 2328, 1842, 2506, 1446, 1860, 2305, 2488, 1831, 2456, 2434, 3035, 737, 1577, 1582, 2011, 1818, 2500, 2137, 2634, 1814, 2115, 2477, 2611, 3121, 3328, 3346, 3455],
  #[252, 795, 793, 1036, 1470, 1862, 1838, 2121, 552, 924, 918, 1160, 1592, 1982, 1958, 2241, 372, 915, 913, 1156, 2281, 2489, 2483, 2613, 912, 1154, 1152, 1272, 2481, 2607, 2601, 2721],
  #[728, 1575, 1816, 2117, 1807, 2450, 3124, 3329, 1568, 1980, 2475, 2605, 2088, 2580, 3296, 3423, 855, 1695, 1936, 2237, 2410, 3011, 3340, 3454, 1934, 2235, 2595, 2715, 3290, 3421, 3568, 3688],
  #[243, 1530, 507, 1652, 748, 1847, 883, 1967, 746, 1841, 877, 1961, 984, 2081, 1120, 2201, 483, 1650, 1323, 1770, 1603, 2146, 1723, 2266, 1597, 2122, 1717, 2242, 2080, 2800, 2200, 2920],
  #[724, 1823, 1579, 2140, 1564, 2497, 1962, 2623, 1800, 3128, 2428, 3347, 2065, 3274, 2562, 3405, 859, 1943, 1699, 2260, 1938, 2617, 2257, 2737, 2402, 3317, 3003, 3450, 3268, 3586, 3403, 3706],
  #[722, 1817, 1573, 2116, 1801, 3130, 2426, 3323, 1562, 2473, 1956, 2599, 2064, 3272, 2556, 3399, 853, 1937, 1693, 2236, 2404, 3341, 3005, 3452, 1932, 2593, 2233, 2713, 3266, 3562, 3397, 3682],
  #[960, 2057, 2056, 2776, 2041, 3250, 3244, 3580, 2040, 3248, 3242, 3556, 2760, 3528, 3504, 3753, 1096, 2177, 2176, 2896, 2538, 3381, 3379, 3700, 2532, 3375, 3373, 3676, 3480, 3729, 3723, 3930],
  #[120, 651, 627, 1473, 271, 779, 755, 1595, 270, 777, 753, 1593, 390, 897, 873, 1713, 603, 1449, 1443, 2352, 1458, 1867, 1843, 2504, 1452, 1861, 1837, 2480, 2307, 2464, 2440, 3041],
  #[247, 773, 1482, 1869, 529, 906, 1604, 1989, 768, 1010, 1834, 2099, 895, 1138, 1954, 2219, 731, 1571, 1819, 2498, 1580, 1987, 2136, 2628, 1808, 2091, 3123, 3304, 2453, 2587, 3344, 3431],
  #[246, 771, 1476, 1863, 769, 1012, 1832, 2097, 528, 900, 1598, 1983, 894, 1136, 1952, 2217, 729, 1569, 1813, 2474, 1810, 2093, 3125, 3305, 1574, 1981, 2112, 2604, 2451, 2581, 3320, 3425],
  #[366, 891, 2283, 2465, 889, 1132, 2459, 2589, 888, 1130, 2457, 2583, 1128, 1248, 2577, 2697, 849, 1689, 2416, 3017, 1930, 2213, 3338, 3430, 1928, 2211, 3314, 3424, 2571, 2691, 3544, 3664],
  #[241, 1506, 749, 1845, 505, 1628, 882, 1965, 744, 1835, 986, 2075, 871, 1955, 1114, 2195, 725, 1821, 1565, 2496, 1578, 2138, 1963, 2622, 1802, 3129, 2067, 3280, 2429, 3345, 2563, 3407],
  #[481, 1626, 1602, 2144, 1321, 1746, 1722, 2264, 1591, 2098, 2074, 2794, 1711, 2218, 2194, 2914, 858, 1941, 1939, 2616, 1698, 2258, 2256, 2736, 2400, 3293, 3269, 3584, 3001, 3426, 3402, 3704],
  #[720, 1811, 1803, 3136, 1567, 2092, 2424, 3299, 1560, 2449, 2066, 3273, 1950, 2575, 2550, 3393, 962, 2051, 2043, 3256, 2050, 2770, 3245, 3578, 2042, 3249, 2762, 3552, 3240, 3532, 3506, 3759],
  #[847, 1931, 2405, 3339, 1687, 2212, 3004, 3428, 1926, 2569, 3264, 3538, 2209, 2689, 3391, 3658, 1090, 2171, 2539, 3383, 2170, 2890, 3378, 3698, 2526, 3369, 3482, 3735, 3367, 3652, 3721, 3906],
  #[240, 1500, 747, 1839, 745, 1833, 988, 2073, 504, 1622, 876, 1959, 870, 1953, 1112, 2193, 723, 1815, 1563, 2472, 1804, 3131, 2069, 3281, 1572, 2114, 1957, 2598, 2427, 3321, 2557, 3401],
  #[721, 1809, 1805, 3137, 1561, 2448, 2068, 3275, 1566, 2090, 2425, 3297, 1951, 2574, 2551, 3395, 964, 2049, 2045, 3257, 2044, 3251, 2764, 3576, 2048, 2768, 3243, 3554, 3241, 3530, 3508, 3765],
  #[480, 1620, 1596, 2120, 1590, 2096, 2072, 2792, 1320, 1740, 1716, 2240, 1710, 2216, 2192, 2912, 852, 1935, 1933, 2592, 2401, 3291, 3267, 3560, 1692, 2234, 2232, 2712, 3000, 3420, 3396, 3680],
  #[846, 1929, 2403, 3315, 1927, 2568, 3265, 3536, 1686, 2210, 3002, 3422, 2208, 2688, 3390, 3656, 1088, 2169, 2533, 3377, 2527, 3371, 3484, 3741, 2168, 2888, 3372, 3674, 3366, 3650, 3720, 3900],
  #[360, 2289, 867, 2441, 865, 2435, 1108, 2565, 864, 2433, 1106, 2559, 1104, 2553, 1224, 2673, 843, 2417, 1683, 3016, 1924, 3336, 2189, 3406, 1922, 3312, 2187, 3400, 2547, 3520, 2667, 3640],
  #[841, 2411, 1925, 3337, 1681, 3010, 2188, 3404, 1920, 3288, 2545, 3514, 2185, 3394, 2665, 3634, 1084, 2541, 2165, 3382, 2164, 3380, 2884, 3696, 2520, 3488, 3363, 3733, 3361, 3727, 3628, 3882],
  #[840, 2409, 1923, 3313, 1921, 3289, 2544, 3512, 1680, 3008, 2186, 3398, 2184, 3392, 2664, 3632, 1082, 2535, 2163, 3376, 2521, 3490, 3365, 3739, 2162, 3374, 2882, 3672, 3360, 3726, 3626, 3876],
  #[1080, 2529, 2523, 3496, 2161, 3370, 3364, 3738, 2160, 3368, 3362, 3732, 2880, 3648, 3624, 3870, 1200, 2649, 2643, 3616, 2641, 3610, 3604, 3858, 2640, 3608, 3602, 3852, 3600, 3846, 3840, 3960]]

private def decode (m : Nat) (i : Fin 10) : Bool := m.testBit i

private def packBits (c : Fin 10 → Bool) : List (Fin 10) → Nat
  | [] => 0
  | k :: ks => 2 * packBits c ks + if c k then 1 else 0

private theorem packBits_lt (c : Fin 10 → Bool) (ks : List (Fin 10)) :
    packBits c ks < 2^ks.length := by
  induction ks with
  | nil => simp [packBits]
  | cons k ks ih =>
    simp only [packBits, List.length_cons, pow_succ]
    split <;> omega

private theorem packBits_bit (c : Fin 10 → Bool) (ks : List (Fin 10))
    (j : Nat) (hj : j < ks.length) : (packBits c ks).testBit j = c (ks[j]'hj) := by
  induction ks generalizing j with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero =>
      cases h : c k <;> simp [packBits, h, Nat.testBit_eq_decide_div_mod_eq]
    | succ j =>
      rw [Nat.testBit_succ, packBits]
      have hd : (2 * packBits c ks + (if c k then 1 else 0))/2 = packBits c ks := by
        split <;> omega
      rw [hd]
      exact ih j (by simpa using hj)

private def encode (c : Fin 10 → Bool) : Fin 1024 :=
  ⟨packBits c (List.finRange 10), by simpa using packBits_lt c (List.finRange 10)⟩

private theorem encode_correct (c : Fin 10 → Bool) (i : Fin 10) : decode (encode c) i = c i := by
  simpa [decode,encode] using packBits_bit c (List.finRange 10) i
    (by simpa using i.isLt)

private def packed (m : Fin 1024) : Nat :=
  (caseWitnesses.getD (m.val / 32) #[]).getD (m.val % 32) 0

private def caseId (m : Fin 1024) : Fin 34 :=
  ⟨packed m / 120 % 34, Nat.mod_lt _ (by decide)⟩

private def permutationValue (k : Fin 120) (i : Fin 5) : Fin 5 :=
  ⟨permutationCodes.getD k 0 / (5^(i : Nat)) % 5, Nat.mod_lt _ (by decide)⟩

private def renumber (m : Fin 1024) (i : Fin 5) : Fin 5 :=
  permutationValue ⟨packed m % 120,Nat.mod_lt _ (by decide)⟩ i

private def edgePair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

private theorem edgePair_eq : ∀ i j : Fin 5, i ≠ j →
    edgePair (edgeIndex i j) = (i,j) ∨ edgePair (edgeIndex i j) = (j,i) := by decide

private theorem edge_symm : ∀ i j : Fin 5, edgeIndex i j = edgeIndex j i := by decide

private theorem permutationValuesInjective : ∀ (k : Fin 120) (i j : Fin 5),
    permutationValue k i = permutationValue k j → i = j := by
  decide +kernel

private theorem correctLabels : ∀ (m : Fin 1024) (k : Fin 10),
    decode m (edgeIndex (renumber m (edgePair k).1) (renumber m (edgePair k).2))
      = twoPatterns (caseId m) k := by
  decide +kernel

private theorem coloring_coverage (m : Fin 1024) :
    (∀ i j : Fin 5, renumber m i = renumber m j → i = j) ∧
    (∀ i j : Fin 5, i ≠ j →
      decode m (edgeIndex (renumber m i) (renumber m j)) = twoPatterns (caseId m) (edgeIndex i j)) := by
  refine ⟨permutationValuesInjective _,?_⟩
  intro i j hij
  have h := correctLabels m (edgeIndex i j)
  rcases edgePair_eq i j hij with hpair | hpair
  · simpa only [hpair] using h
  · simpa only [hpair,edge_symm (renumber m j) (renumber m i)] using h

private theorem canonical_cases (i : Fin 34) (a : ℝ) (ha : 1 < a)
    (h : StandardDistanceData (fromColor (twoPatterns i) 1 a)) : False := by
  fin_cases i
  · exact twoCase0 a ha h
  · exact twoCase1 a ha h
  · exact twoCase2 a ha h
  · exact twoCase3 a ha h
  · exact twoCase4 a ha h
  · exact twoCase5 a ha h
  · exact twoCase6 a ha h
  · exact twoCase7 a ha h
  · exact twoCase8 a ha h
  · exact twoCase9 a ha h
  · exact twoCase10 a ha h
  · exact twoCase11 a ha h
  · exact twoCase12 a ha h
  · exact twoCase13 a ha h
  · exact twoCase14 a ha h
  · exact twoCase15 a ha h
  · exact twoCase16 a ha h
  · exact twoCase17 a ha h
  · exact twoCase18 a ha h
  · exact twoCase19 a ha h
  · exact twoCase20 a ha h
  · exact twoCase21 a ha h
  · exact twoCase22 a ha h
  · exact twoCase23 a ha h
  · exact twoCase24 a ha h
  · exact twoCase25 a ha h
  · exact twoCase26 a ha h
  · exact twoCase27 a ha h
  · exact twoCase28 a ha h
  · exact twoCase29 a ha h
  · exact twoCase30 a ha h
  · exact twoCase31 a ha h
  · exact twoCase32 a ha h
  · exact twoCase33 a ha h


private theorem collinear_of_area_zero {o a b : Point} (hoa : a ≠ o)
    (h : area o a b = 0) : Collinear ℝ ({o,a,b} : Set Point) := by
  have param : ∃ s : ℝ, b 0 = s*(a 0-o 0)+o 0 ∧ b 1 = s*(a 1-o 1)+o 1 := by
    unfold area at h
    by_cases hx : a 0 = o 0
    · have hy : a 1 ≠ o 1 := by
        intro h'
        apply hoa
        ext i
        fin_cases i
        · exact hx
        · exact h'
      have he : b 0 = o 0 := by
        have hv : (a 1-o 1)*(b 0-o 0) = 0 := by simpa [hx] using h
        exact sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr hy))
      refine ⟨(b 1-o 1)/(a 1-o 1), ?_, ?_⟩
      · simp [hx, he]
      · field_simp [sub_ne_zero.mpr hy]
        ring
    · refine ⟨(b 0-o 0)/(a 0-o 0), ?_, ?_⟩
      · field_simp [sub_ne_zero.mpr hx]
        ring
      · field_simp [sub_ne_zero.mpr hx]
        linear_combination h
  obtain ⟨r,hx,hy⟩ := param
  apply (collinear_iff_of_mem (p₀ := o) (by simp : o ∈ ({o,a,b} : Set Point))).mpr
  refine ⟨a-o, ?_⟩
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨r, ?_⟩
    ext i
    fin_cases i
    · exact hx
    · exact hy

private theorem center_of_liftedArea_zero {o a b c : Point}
    (hn : area o a b ≠ 0) (hc : liftedArea o a b c = 0) :
    ∃ z : Point, (∀ p ∈ ({o,a,b,c} : Set Point), dist p z = dist o z) := by
  let A := area o a b
  let xx := (dist a o ^ 2 * (b 1 - o 1) - dist b o ^ 2 * (a 1 - o 1)) / (2*A)
  let yy := ((a 0 - o 0) * dist b o ^ 2 - (b 0 - o 0) * dist a o ^ 2) / (2*A)
  let z := xy (o 0 + xx) (o 1 + yy)
  have hz (p : Point) (hp : dist p o ^ 2 = 2*((p 0-o 0)*xx + (p 1-o 1)*yy)) :
      dist p z = dist o z := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [dist_sq_xy, dist_sq_xy]
    simp only [z, xy_zero, xy_one]
    rw [dist_sq_xy] at hp
    linear_combination hp
  have hclaim (p : Point) (hp : liftedArea o a b p = 0) :
      dist p o ^ 2 = 2*((p 0-o 0)*xx + (p 1-o 1)*yy) := by
    dsimp [xx,yy]
    have hA : A ≠ 0 := hn
    field_simp [hA]
    dsimp [A]
    unfold liftedArea area at hp
    unfold area
    linear_combination hp
  refine ⟨z, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h | h
  · rw [h]
  · rw [h]
    apply hz; apply hclaim
    unfold liftedArea area
    ring
  · rw [h]
    apply hz; apply hclaim
    unfold liftedArea area
    ring
  · rw [h]
    exact hz c (hclaim c hc)

private theorem triangle_formula (o a b : Point) :
    trianglePolynomial (dist o a ^ 2) (dist o b ^ 2) (dist a b ^ 2) =
      4 * area o a b ^ 2 := by
  simp only [trianglePolynomial, area, dist_sq_xy]
  ring

private theorem circle_formula (o a b c : Point) :
    circlePolynomial (dist o a ^ 2) (dist o b ^ 2) (dist o c ^ 2)
      (dist a b ^ 2) (dist a c ^ 2) (dist b c ^ 2) =
      -4 * liftedArea o a b c ^ 2 := by
  simp only [circlePolynomial, liftedArea, area, dist_sq_xy]
  ring

private theorem data_of_points (p : Config 5) (hi : Function.Injective p)
    (hgp : InGeneralPosition p.toFinset) (d0 : ℝ) (hd0 : d0 ≠ 0) :
    StandardDistanceData (fun i j => dist (p i) (p j) ^ 2 / d0) := by
  classical
  let d := fun i j => dist (p i) (p j) ^ 2
  let d' : Fin 5 → Fin 5 → ℝ := fun i j => d i j / d0
  change StandardDistanceData d'
  have hc (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      area (p i) (p j) (p k) ≠ 0 := by
    intro h
    exact hgp.1 (image_contains p i) (image_contains p j) (image_contains p k)
      (fun h => hij (hi h)) (fun h => hjk (hi h)) (fun h => hik (hi h))
      (collinear_of_area_zero (fun h => hij (hi h.symm)) h)
  have gscale (o i j : Fin 5) :
      squaredGram d' o i j = squaredGram d o i j / d0 := by
    unfold squaredGram d' 
    ring
  have gdot (o i j : Fin 5) :
      squaredGram d o i j = 2 * ((p i 0 - p o 0)*(p j 0 - p o 0) +
        (p i 1 - p o 1)*(p j 1 - p o 1)) := by
    simp only [squaredGram, d, dist_sq_xy]
    ring
  constructor
  · intro o i j k l
    simp only [gscale, gdot, div_eq_mul_inv]
    ring
  · intro i j k hij hik hjk hz
    unfold trianglePolynomial d' d at hz
    field_simp [hd0] at hz
    have hz' : trianglePolynomial (dist (p i) (p j)^2)
        (dist (p i) (p k)^2) (dist (p j) (p k)^2) = 0 := by
      unfold trianglePolynomial
      linear_combination hz
    rw [triangle_formula] at hz'
    exact hc i j k hij hik hjk (by nlinarith only [hz'])
  · intro i j k l hij hik hil hjk hjl hkl hz
    unfold circlePolynomial d' d at hz
    field_simp [hd0] at hz
    have hz' : circlePolynomial (dist (p i) (p j)^2)
        (dist (p i) (p k)^2) (dist (p i) (p l)^2)
        (dist (p j) (p k)^2) (dist (p j) (p l)^2) (dist (p k) (p l)^2) = 0 := by
      unfold circlePolynomial
      linear_combination hz
    rw [circle_formula] at hz'
    have hlift : liftedArea (p i) (p j) (p k) (p l) = 0 := by
      nlinarith only [hz']
    obtain ⟨z, hz⟩ := center_of_liftedArea_zero (hc i j k hij hik hjk) hlift
    have hne (a b : Fin 5) (hab : a ≠ b) : p a ≠ p b := fun h => hab (hi h)
    let U : Finset Point := {p i,p j,p k,p l}
    have hU : U ⊆ p.toFinset := by
      intro y hy
      simp [U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> exact image_contains p _
    have hcard : U.card = 4 :=
      Finset.card_eq_four.mpr ⟨_,_,_,_,hne _ _ hij,hne _ _ hik,hne _ _ hil,
        hne _ _ hjk,hne _ _ hjl,hne _ _ hkl,rfl⟩
    apply hgp.2 U hU hcard
    refine ⟨z,dist (p i) z,?_⟩
    intro y hy
    exact hz y (by simpa [U] using hy)

private theorem apply_coloring (a : ℝ) (ha : 1 < a) (c : Fin 10 → Bool)
    (h : StandardDistanceData (fromColor c 1 a)) : False := by
  let m := encode c
  obtain ⟨hinj, hcolors⟩ := coloring_coverage m
  let e := renumber m
  have hd (i j : Fin 5) :
      fromColor c 1 a (e i) (e j) = fromColor (twoPatterns (caseId m)) 1 a i j := by
    by_cases hij : i=j
    · subst j
      simp [fromColor]
    · have he : e i ≠ e j := fun h => hij (hinj i j h)
      have hc := hcolors i j hij
      rw [encode_correct c] at hc
      change c (edgeIndex (e i) (e j)) = _ at hc
      simp [fromColor, he, hij, hc]
  apply canonical_cases (caseId m) a ha
  constructor
  · intro o i j k l
    have hh := h.gram (e o) (e i) (e j) (e k) (e l)
    simpa only [squaredGram, hd] using hh
  · intro i j k hij hik hjk
    have hh := h.triangle (e i) (e j) (e k) (fun h => hij (hinj i j h))
      (fun h => hik (hinj i k h)) (fun h => hjk (hinj j k h))
    simpa only [hd] using hh
  · intro i j k l hij hik hil hjk hjl hkl
    have hh := h.circle (e i) (e j) (e k) (e l) (fun h => hij (hinj i j h))
      (fun h => hik (hinj i k h)) (fun h => hil (hinj i l h))
      (fun h => hjk (hinj j k h)) (fun h => hjl (hinj j l h)) (fun h => hkl (hinj k l h))
    simpa only [hd] using hh

private theorem two_distance_lower (p : Config 5) (hi : Function.Injective p)
    (hgp : InGeneralPosition p.toFinset) : 3 ≤ distinctDistances p.toFinset := by
  classical
  let D := p.toFinset.offDiag.image (fun pair : Point × Point => dist pair.1 pair.2)
  change 3 ≤ D.card
  by_contra! hsmall
  have in_D (i j : Fin 5) (hij : i ≠ j) : dist (p i) (p j) ∈ D :=
    Finset.mem_image.mpr ⟨(p i, p j), Finset.mem_offDiag.mpr
      ⟨image_contains p i, image_contains p j, fun h => hij (hi h)⟩, rfl⟩
  have pos_D {d : ℝ} (hd : d ∈ D) : 0 < d := by
    obtain ⟨⟨u,v⟩, hpair, rfl⟩ := Finset.mem_image.mp hd
    exact dist_pos.mpr (Finset.mem_offDiag.mp hpair).2.2
  have hpos : 0 < D.card :=
    Finset.card_pos.mpr ⟨_,in_D 0 1 (by decide)⟩
  have hrs : ∃ r s : ℝ, 0 < r ∧ r < s ∧ ∀ d ∈ D, d = r ∨ d = s := by
    have hcase : D.card = 1 ∨ D.card = 2 := by omega
    rcases hcase with hc | hc
    · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc
      have hp : 0 < r := pos_D (by simp [hr])
      refine ⟨r,r+1,hp,by linarith,?_⟩
      intro x hx
      exact Or.inl (by simpa [hr] using hx)
    · obtain ⟨r,s,hrs,hD⟩ := Finset.card_eq_two.mp hc
      rcases lt_or_gt_of_ne hrs with hr | hr
      · refine ⟨r,s,pos_D (by simp [hD]),hr,?_⟩
        intro d hd
        simpa [hD] using hd
      · refine ⟨s,r,pos_D (by simp [hD]),hr,?_⟩
        intro d hd
        simpa [hD, or_comm] using hd
  obtain ⟨r,s,hr,hrs,hd⟩ := hrs
  let a := s^2/r^2
  have hrr : 0 < r^2 := by positivity
  have haa : 1 < a := by
    apply (lt_div_iff₀ hrr).mpr
    have hsum : 0 < s + r := by linarith
    have hp := mul_pos (sub_pos.mpr hrs) hsum
    nlinarith only [hp]
  let c : Fin 10 → Bool := fun k =>
    decide (dist (p (edgePair k).1) (p (edgePair k).2) = s)
  have hmatrix (i j : Fin 5) :
      (dist (p i) (p j))^2/r^2 = fromColor c 1 a i j := by
    by_cases hij : i=j
    · subst j
      simp [fromColor]
    · have heq : c (edgeIndex i j) = decide (dist (p i) (p j) = s) := by
        rcases edgePair_eq i j hij with h | h
        · simp [c,h]
        · simp [c,h,dist_comm]
      rcases hd _ (in_D i j hij) with h | h
      · have hn : dist (p i) (p j) ≠ s := by rw [h]; exact hrs.ne
        simp [fromColor,hij,heq,h,hrs.ne,hrr.ne']
      · simp [fromColor,hij,heq,h,a]
  have rd := data_of_points p hi hgp (r^2) hrr.ne'
  have heq : (fun i j => (dist (p i) (p j))^2/r^2) = fromColor c 1 a := by
    funext i j
    exact hmatrix i j
  rw [heq] at rd
  exact apply_coloring a haa c rd

end Esgk

open Esgk in
theorem solution :
    (∀ p : Config 5, Function.Injective p → InGeneralPosition p.toFinset →
      3 ≤ distinctDistances p.toFinset) ∧
      ∃ p : Config 5, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
        distinctDistances p.toFinset = 3 :=
  ⟨Esgk.two_distance_lower, Esgk.five_witness⟩

#print axioms solution
