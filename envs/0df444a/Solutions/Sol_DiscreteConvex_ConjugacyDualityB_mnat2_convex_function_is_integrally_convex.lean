-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.mnat2_convex_function_is_integrally_convex
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T03:24:12.256992+00:00
-- url     : https://prove2.me/submissions/1e573557-f601-476b-96d3-85ca0d319c53

import Mathlib
import Theorems.Thm_LP_strong_duality_matrix
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvexFunction
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNatConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntEmbed
import Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_intersection_hull
import Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mnat_convex_local_representation

open scoped BigOperators
open Matrix
open Classical DiscreteConvex.ConjugacyDualityB

namespace ConjugacyFunctionProof

variable {V : Type*} [Fintype V]

private def affine (a : Option V → ℝ) (x : V → ℝ) : ℝ :=
  a none + ∑ v, a (some v) * x v

private lemma sum_affine {ι : Type*} [Fintype ι]
    (a : Option V → ℝ) (X : ι → V → ℝ) (μ : ι → ℝ) (p : V → ℝ)
    (h1 : ∑ i, μ i = 1) (hp : ∀ v, ∑ i, μ i * X i v = p v) :
    ∑ i, μ i * affine a (X i) = affine a p := by
  simp only [affine, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, h1, one_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  calc
    ∑ i, μ i * (a (some v) * X i v) =
        a (some v) * ∑ i, μ i * X i v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a (some v) * p v := by rw [hp]

/-- Finite affine support with a convex combination supported on its tight face. -/
private lemma finite_affine_support {ι : Type*} [Fintype ι]
    (X : ι → V → ℝ) (r : ι → ℝ) (p : V → ℝ)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (h1 : ∑ i, μ i = 1)
    (hp : ∀ v, ∑ i, μ i * X i v = p v) :
    ∃ (a : Option V → ℝ) (ν : ι → ℝ),
      (∀ i, 0 ≤ ν i) ∧ (∑ i, ν i = 1) ∧
      (∀ v, ∑ i, ν i * X i v = p v) ∧
      (∀ i, affine a (X i) ≤ r i) ∧
      (∀ i, 0 < ν i → affine a (X i) = r i) := by
  classical
  let A : Matrix ι (Option V) ℝ := fun i o => o.elim 1 (X i)
  let c : Option V → ℝ := fun o => o.elim 1 p
  obtain ⟨M, hM⟩ := (Set.finite_range r).bddBelow
  have hP : ∃ x, A *ᵥ x ≤ r := by
    refine ⟨fun o => o.elim M (fun _ => 0), ?_⟩
    intro i
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_option, A] using hM ⟨i, rfl⟩
  have hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c := by
    refine ⟨μ, hμ, ?_⟩
    funext o
    cases o with
    | none =>
      change ∑ i, (1 : ℝ) * μ i = 1
      simpa using h1
    | some v =>
      change ∑ i, X i v * μ i = p v
      simpa [mul_comm] using hp v
  obtain ⟨a, ν, ha, hν, hdual, heq, _⟩ := LP.strong_duality_matrix A r c hP hD
  have hν1 : ∑ i, ν i = 1 := by
    have h := congrFun hdual none
    change ∑ i, (1 : ℝ) * ν i = 1 at h
    simpa using h
  have hνp : ∀ v, ∑ i, ν i * X i v = p v := by
    intro v
    have h := congrFun hdual (some v)
    change ∑ i, X i v * ν i = p v at h
    simpa [mul_comm] using h
  have hab : ∀ i, affine a (X i) ≤ r i := by
    intro i
    simpa [affine, Matrix.mulVec, dotProduct, Fintype.sum_option, A, mul_comm] using ha i
  have heq' : affine a p = ∑ i, ν i * r i := by
    simpa [affine, dotProduct, Fintype.sum_option, c, mul_comm] using heq
  have hzero : ∑ i, ν i * (r i - affine a (X i)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sum_affine a X ν p hν1 hνp, ← heq']
    ring
  have heach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hν i) (sub_nonneg.mpr (hab i)))).mp hzero
  refine ⟨a, ν, hν, hν1, hνp, hab, ?_⟩
  intro i hi
  have h := heach i (Finset.mem_univ i)
  have hz : r i - affine a (X i) = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt hi)
  linarith

variable [DecidableEq V]

private def liftZ (z : V → ℤ) : Option V → ℤ
  | none => - ∑ v, z v
  | some v => z v

private def liftR : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) where
  toFun p := fun o => match o with | none => - ∑ v, p v | some v => p v
  map_add' p q := by
    funext o; cases o <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' a p := by
    funext o; cases o <;> simp [Finset.mul_sum]

private def projectR : (Option V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun p := fun v => p (some v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma lift_cast (z : V → ℤ) :
    liftR (fun v => (z v : ℝ)) = fun o => (liftZ z o : ℝ) := by
  funext o; cases o <;> simp [liftR, liftZ]

private lemma lift_embed (D : Set (V → ℤ)) :
    liftR '' IntEmbed D = DiscreteConvex.MConvexSetsB.IntEmbed (LiftedSet D) := by
  ext p
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨liftZ z, ⟨by simp [liftZ], hz⟩, (lift_cast z).symm⟩
  · rintro ⟨z, ⟨hs, hz⟩, rfl⟩
    refine ⟨fun v => (z (some v) : ℝ), ⟨fun v => z (some v), hz, rfl⟩, ?_⟩
    funext o; cases o with
    | none => simpa [liftR] using congrArg (fun t : ℤ => (t : ℝ)) hs.symm
    | some v => rfl


private lemma exchange_convert (D : Set (V → ℤ)) (h : MNatConvexSet D) :
    DiscreteConvex.MConvexSetsB.ExchangeAxiomB (LiftedSet D) := by
  simpa [MNatConvexSet, ExchangeAxiomB, SuppPos, SuppNeg, IndicatorVec,
    DiscreteConvex.MConvexSetsB.ExchangeAxiomB, DiscreteConvex.MConvexSetsB.SuppPos, DiscreteConvex.MConvexSetsB.SuppNeg, DiscreteConvex.MConvexSetsB.CharVec] using h


private lemma hull_nonempty (B : Set (Option V → ℤ)) {p : Option V → ℝ}
    (hp : p ∈ convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed B)) : B.Nonempty := by
  have h := convexHull_nonempty_iff.mp (show (convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed B)).Nonempty from ⟨p, hp⟩)
  exact Set.image_nonempty.mp h


private lemma lifted_hull (D : Set (V → ℤ)) {p : V → ℝ}
    (hp : p ∈ convexHull ℝ (IntEmbed D)) :
    liftR p ∈ convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed (LiftedSet D)) := by
  rw [← lift_embed, ← LinearMap.image_convexHull]
  exact ⟨p, hp, rfl⟩


private lemma mnat_intersection_hull_mem (D1 D2 : Set (V → ℤ))
    (h1 : MNatConvexSet D1) (h2 : MNatConvexSet D2) (p : V → ℝ)
    (hp1 : p ∈ convexHull ℝ (IntEmbed D1)) (hp2 : p ∈ convexHull ℝ (IntEmbed D2)) :
    p ∈ convexHull ℝ (IntEmbed (D1 ∩ D2)) := by
  have h1p := lifted_hull D1 hp1
  have h2p := lifted_hull D2 hp2
  have hboth : liftR p ∈ convexHull ℝ
      (DiscreteConvex.MConvexSetsB.IntEmbed (LiftedSet D1 ∩ LiftedSet D2)) := by
    rw [DiscreteConvex.MConvexSetsB.mconvex_intersection_hull _ _
      (exchange_convert D1 h1) (exchange_convert D2 h2)
      (hull_nonempty _ h1p) (hull_nonempty _ h2p)]
    exact ⟨h1p, h2p⟩
  have hproject : projectR '' DiscreteConvex.MConvexSetsB.IntEmbed
      (LiftedSet D1 ∩ LiftedSet D2) ⊆ IntEmbed (D1 ∩ D2) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨fun v => z (some v), ⟨hz.1.2, hz.2.2⟩, rfl⟩
  apply convexHull_mono hproject
  rw [← LinearMap.image_convexHull]
  exact ⟨liftR p, hboth, rfl⟩

private lemma hull_of_positive_weights {ι : Type*} [Fintype ι]
    (X : ι → V → ℝ) (μ : ι → ℝ) (p : V → ℝ) (A : Set (V → ℝ))
    (hμ : ∀ i, 0 ≤ μ i) (h1 : ∑ i, μ i = 1)
    (hp : ∀ v, ∑ i, μ i * X i v = p v)
    (hA : ∀ i, 0 < μ i → X i ∈ A) : p ∈ convexHull ℝ A := by
  classical
  have hi : ∃ i, 0 < μ i := by
    by_contra! hn
    have hs : ∑ i, μ i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i0, hi0⟩ := hi
  let Y : ι → V → ℝ := fun i => if 0 < μ i then X i else X i0
  apply mem_convexHull_of_exists_fintype μ Y hμ h1
  · intro i
    dsimp [Y]
    split_ifs with h
    · exact hA i h
    · exact hA i0 hi0
  · funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      ∑ i, μ i * Y i v = ∑ i, μ i * X i v := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : 0 < μ i
        · simp [Y, h]
        · have hz : μ i = 0 := le_antisymm (le_of_not_gt h) (hμ i)
          simp [hz]
      _ = p v := hp v

private lemma affine_compare_hull (a b c : Option V → ℝ) (A : Set (V → ℝ))
    (hA : ∀ x ∈ A, affine a x ≤ affine b x + affine c x)
    (p : V → ℝ) (hp : p ∈ convexHull ℝ A) :
    affine a p ≤ affine b p + affine c p := by
  obtain ⟨ι, inst, μ, X, hμ, h1, hX, hmean⟩ := mem_convexHull_iff_exists_fintype.mp hp
  letI := inst
  have hm : ∀ v, ∑ i, μ i * X i v = p v := by
    intro v
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hmean v
  calc
    affine a p = ∑ i, μ i * affine a (X i) := (sum_affine a X μ p h1 hm).symm
    _ ≤ ∑ i, μ i * (affine b (X i) + affine c (X i)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hA _ (hX i)) (hμ i))
    _ = affine b p + affine c p := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, sum_affine b X μ p h1 hm, sum_affine c X μ p h1 hm]

private lemma mix_of_hull_finset (T : Finset (V → ℤ)) (p : V → ℝ)
    (hp : p ∈ convexHull ℝ (IntEmbed (T : Set (V → ℤ)))) :
    ∃ μ : T → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i = 1) ∧
      (∀ v, ∑ i, μ i * (i.val v : ℝ) = p v) := by
  classical
  let e : (V → ℤ) → (V → ℝ) := fun z v => (z v : ℝ)
  have hinj : Function.Injective e := by
    intro x y h
    funext v
    have hv := congrFun h v
    change (x v : ℝ) = (y v : ℝ) at hv
    exact_mod_cast hv
  have heq : IntEmbed (T : Set (V → ℤ)) = (T.image e : Set (V → ℝ)) := by
    ext x
    simp only [IntEmbed, Set.mem_image, Finset.mem_coe, Finset.mem_image]
    rfl
  rw [heq] at hp
  obtain ⟨w, hw, hw1, hwp⟩ := Finset.mem_convexHull.mp hp
  have hs : ∑ z ∈ T, w (e z) = 1 := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hw1
    exact hw1
  refine ⟨fun i => w (e i.val), ?_, ?_, ?_⟩
  · intro i
    exact hw _ (Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩)
  · exact (Finset.sum_coe_sort T (fun z => w (e z))).trans hs
  · intro v
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hwp
    have hv := congrFun hwp v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id_eq] at hv
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hv
    change ∑ i : T, (fun z : V → ℤ => w (e z) * (z v : ℝ)) i.val = p v
    exact (Finset.sum_coe_sort T (fun z : V → ℤ => w (e z) * (z v : ℝ))).trans hv

private def inBox (a b : V → ℤ) (z : Option V → ℤ) : Prop :=
  ∀ v, a v ≤ z (some v) ∧ z (some v) ≤ b v

private lemma move_box (a b : V → ℤ) (x y : Option V → ℤ)
    (hx : inBox a b x) (hy : inBox a b y) (u v : Option V)
    (hu : y u < x u) (hv : x v < y v) :
    inBox a b (fun w => x w - DiscreteConvex.MConvexSetsB.CharVec u w + DiscreteConvex.MConvexSetsB.CharVec v w) := by
  have huv : u ≠ v := by intro h; subst v; omega
  intro w
  have h1 := hx w
  have h2 := hy w
  by_cases hwu : some w = u
  · subst u
    simp only [DiscreteConvex.MConvexSetsB.CharVec, huv, if_true, if_false]
    omega
  · by_cases hwv : some w = v
    · subst v
      simp only [DiscreteConvex.MConvexSetsB.CharVec, hwu, if_true, if_false]
      omega
    · simpa [DiscreteConvex.MConvexSetsB.CharVec, hwu, hwv] using h1


private noncomputable def localSet (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : Finset (V → ℤ) :=
  (IntegralNeighborhoodFinset p).filter (fun y => y ∈ DomZ f)

private def tightSet (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ)
    (a : Option V → ℝ) : Set (V → ℤ) :=
  {z | z ∈ localSet f p ∧ affine a (fun v => (z v : ℝ)) = (f z).untopD 0}

private lemma coe_value {t : WithTop ℝ} (ht : t ≠ ⊤) :
    ((t.untopD 0 : ℝ) : WithTop ℝ) = t := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [← hr]
  rfl

private lemma real_add_le {a b c d : WithTop ℝ}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (h : a + b ≤ c + d) :
    a.untopD 0 + b.untopD 0 ≤ c.untopD 0 + d.untopD 0 := by
  apply WithTop.coe_le_coe.mp
  simpa only [WithTop.coe_add, coe_value ha, coe_value hb, coe_value hc, coe_value hd] using h

private lemma lifted_finite (f : (V → ℤ) → WithTop ℝ) (z : Option V → ℤ)
    (h : LiftedFunction f z ≠ ⊤) :
    z none = -(∑ v, z (some v)) ∧ f (fun v => z (some v)) ≠ ⊤ := by
  by_cases hs : z none = -(∑ v, z (some v))
  · exact ⟨hs, by simpa only [LiftedFunction, if_pos hs] using h⟩
  · simp only [LiftedFunction, if_neg hs, ne_eq, not_true_eq_false] at h

private lemma affine_pair (a : Option V → ℝ) (x y x' y' : V → ℝ)
    (h : ∀ v, x' v + y' v = x v + y v) :
    affine a x' + affine a y' = affine a x + affine a y := by
  have hs : (∑ v, a (some v) * x' v) + (∑ v, a (some v) * y' v) =
      (∑ v, a (some v) * x v) + (∑ v, a (some v) * y v) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    simpa only [mul_add] using congrArg (fun t => a (some v) * t) (h v)
  dsimp [affine]
  linarith

private lemma move_nbhd (p : V → ℝ) (x y : Option V → ℤ)
    (hx : (fun v => x (some v)) ∈ IntegralNeighborhoodFinset p)
    (hy : (fun v => y (some v)) ∈ IntegralNeighborhoodFinset p)
    (u v : Option V) (hu : y u < x u) (hv : x v < y v) :
    (fun w => x (some w) - IndicatorVec {u} (some w) + IndicatorVec {v} (some w)) ∈
      IntegralNeighborhoodFinset p := by
  have hxb : inBox (fun v => ⌊p v⌋) (fun v => ⌈p v⌉) x := by
    simpa [inBox, IntegralNeighborhoodFinset, Fintype.mem_piFinset, Finset.mem_Icc] using hx
  have hyb : inBox (fun v => ⌊p v⌋) (fun v => ⌈p v⌉) y := by
    simpa [inBox, IntegralNeighborhoodFinset, Fintype.mem_piFinset, Finset.mem_Icc] using hy
  have h := move_box _ _ x y hxb hyb u v hu hv
  simpa [inBox, IntegralNeighborhoodFinset, Fintype.mem_piFinset, Finset.mem_Icc,
    IndicatorVec, DiscreteConvex.MConvexSetsB.CharVec] using h

/-- Equality faces of a local affine minorant retain the M-natural exchange axiom. -/
private lemma tight_mnat (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f)
    (p : V → ℝ) (a : Option V → ℝ)
    (hb : ∀ z ∈ localSet f p, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0) :
    MNatConvexSet (tightSet f p a) := by
  intro x hx y hy u hu
  have hxf : f (fun v => x (some v)) ≠ ⊤ := (Finset.mem_filter.mp hx.2.1).2
  have hyf : f (fun v => y (some v)) ≠ ⊤ := (Finset.mem_filter.mp hy.2.1).2
  have hxL : LiftedFunction f x ≠ ⊤ := by
    simpa only [LiftedFunction, if_pos hx.1] using hxf
  have hyL : LiftedFunction f y ≠ ⊤ := by
    simpa only [LiftedFunction, if_pos hy.1] using hyf
  obtain ⟨v, hv, hineq⟩ := hf x hxL y hyL u hu
  let x' : Option V → ℤ := fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w
  let y' : Option V → ℤ := fun w => y w - IndicatorVec {v} w + IndicatorVec {u} w
  have heqy : (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) = y' := by
    funext w
    dsimp [y']
    omega
  rw [heqy] at hineq
  change LiftedFunction f x' + LiftedFunction f y' ≤ LiftedFunction f x + LiftedFunction f y at hineq
  have hsum : LiftedFunction f x' + LiftedFunction f y' ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hxL, hyL⟩) hineq
  have hxfin := lifted_finite f x' (WithTop.add_ne_top.mp hsum).1
  have hyfin := lifted_finite f y' (WithTop.add_ne_top.mp hsum).2
  have hxr : LiftedFunction f x = f (fun v => x (some v)) := by simp only [LiftedFunction, if_pos hx.1]
  have hyr : LiftedFunction f y = f (fun v => y (some v)) := by simp only [LiftedFunction, if_pos hy.1]
  have hxr' : LiftedFunction f x' = f (fun v => x' (some v)) := by simp only [LiftedFunction, if_pos hxfin.1]
  have hyr' : LiftedFunction f y' = f (fun v => y' (some v)) := by simp only [LiftedFunction, if_pos hyfin.1]
  rw [hxr, hyr, hxr', hyr'] at hineq
  have hreal := real_add_le hxfin.2 hyfin.2 hxf hyf hineq
  have hu' : y u < x u := by simpa [SuppPos] using hu
  have hv' : x v < y v := by simpa [SuppNeg] using hv
  have hxN := move_nbhd p x y (Finset.mem_filter.mp hx.2.1).1
    (Finset.mem_filter.mp hy.2.1).1 u v hu' hv'
  have hyN := move_nbhd p y x (Finset.mem_filter.mp hy.2.1).1
    (Finset.mem_filter.mp hx.2.1).1 v u hv' hu'
  have hxt : (fun w => x' (some w)) ∈ localSet f p := Finset.mem_filter.mpr ⟨hxN, hxfin.2⟩
  have hyt : (fun w => y' (some w)) ∈ localSet f p := Finset.mem_filter.mpr ⟨hyN, hyfin.2⟩
  have hpair : affine a (fun w => (x' (some w) : ℝ)) + affine a (fun w => (y' (some w) : ℝ)) =
      affine a (fun w => (x (some w) : ℝ)) + affine a (fun w => (y (some w) : ℝ)) := by
    apply affine_pair
    intro w
    dsimp [x', y']
    push_cast
    ring
  have hxEq : affine a (fun w => (x' (some w) : ℝ)) = (f (fun w => x' (some w))).untopD 0 := by
    have hbx := hb _ hxt
    have hby := hb _ hyt
    have hxe := hx.2.2
    have hye := hy.2.2
    linarith
  have hyEq : affine a (fun w => (y' (some w) : ℝ)) = (f (fun w => y' (some w))).untopD 0 := by
    have hbx := hb _ hxt
    have hby := hb _ hyt
    have hxe := hx.2.2
    have hye := hy.2.2
    linarith
  refine ⟨v, hv, ⟨hxfin.1, hxt, hxEq⟩, ?_⟩
  rw [heqy]
  exact ⟨hyfin.1, hyt, hyEq⟩

-- Finite-infimum helpers adapted from mrfancypants, accepted submission
-- 5ac997fe-8d9b-4700-910b-9f1a12aaa4d9.
private def CCSet (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) : Set (WithTop ℝ) :=
  {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
    L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)}

private lemma ccvOn_eq (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    ConvexClosureValOn f S x = sInf (CCSet f S x) := rfl

private lemma ccset_bddBelow (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    BddBelow (CCSet f S x) := by
  refine ⟨((-(∑ y ∈ S, |(f y).untopD 0|) : ℝ) : WithTop ℝ), ?_⟩
  rintro L ⟨lam, h0, h1, -, -, rfl⟩
  rw [WithTop.coe_le_coe]
  have : ∀ y ∈ S, -|(f y).untopD 0| ≤ lam y * (f y).untopD 0 := by
    intro y hy
    have hl1 : lam y ≤ 1 := (Finset.single_le_sum h0 hy).trans h1.le
    have h2 := mul_le_mul_of_nonneg_left (neg_abs_le ((f y).untopD 0)) (h0 y hy)
    have h3 := mul_le_mul_of_nonneg_right hl1 (abs_nonneg ((f y).untopD 0))
    linarith
  calc -(∑ y ∈ S, |(f y).untopD 0|) = ∑ y ∈ S, -|(f y).untopD 0| := by rw [Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum this

private lemma ccvOn_le_of (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (hd : ∀ y ∈ S, y ∈ DomZ f) (h2 : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) :
    ConvexClosureValOn f S x ≤ ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ) := by
  rw [ccvOn_eq]
  exact csInf_le (ccset_bddBelow f S x) ⟨lam, h0, h1, hd, h2, rfl⟩


private lemma mnat_convert (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    DiscreteConvex.MConvexFunctionsC.MNaturalConvex f := by
  change MExchangeAxiom (LiftedFunction f) at hf
  change DiscreteConvex.MConvexFunctionsC.MExchangeAxiom (LiftedFunction f)
  simpa only [MExchangeAxiom, DomZ, SuppPos, SuppNeg, IndicatorVec,
    DiscreteConvex.MConvexFunctionsC.MExchangeAxiom,
    DiscreteConvex.MConvexFunctionsC.DomZ,
    DiscreteConvex.MConvexFunctionsC.SuppPos,
    DiscreteConvex.MConvexFunctionsC.SuppNeg,
    DiscreteConvex.MConvexFunctionsC.CharVec, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] using hf

private lemma local_rep (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f)
    (p : V → ℝ) (S : Finset (V → ℤ)) (hS : ∀ z ∈ S, z ∈ DomZ f)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ z ∈ S, 0 ≤ lam z) (h1 : ∑ z ∈ S, lam z = 1)
    (hp : ∀ v, ∑ z ∈ S, lam z * (z v : ℝ) = p v) :
    ∃ μ : (V → ℤ) → ℝ,
      (∀ z ∈ localSet f p, 0 ≤ μ z) ∧ (∑ z ∈ localSet f p, μ z = 1) ∧
      (∀ v, ∑ z ∈ localSet f p, μ z * (z v : ℝ) = p v) ∧
      ∑ z ∈ localSet f p, μ z * (f z).untopD 0 ≤ ∑ z ∈ S, lam z * (f z).untopD 0 := by
  exact DiscreteConvex.MConvexFunctionsC.mnat_convex_local_representation
    f (mnat_convert f hf) p S hS lam h0 h1 hp

private lemma local_support (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f)
    (p : V → ℝ) (S : Finset (V → ℤ)) (hS : ∀ z ∈ S, z ∈ DomZ f)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ z ∈ S, 0 ≤ lam z) (h1 : ∑ z ∈ S, lam z = 1)
    (hp : ∀ v, ∑ z ∈ S, lam z * (z v : ℝ) = p v) :
    ∃ a : Option V → ℝ,
      (∀ z ∈ localSet f p, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0) ∧
      p ∈ convexHull ℝ (IntEmbed (tightSet f p a)) ∧
      affine a p ≤ ∑ z ∈ S, lam z * (f z).untopD 0 := by
  obtain ⟨μ, hμ0, hμ1, hμp, hμcost⟩ := local_rep f hf p S hS lam h0 h1 hp
  let T := localSet f p
  let X : T → V → ℝ := fun i v => (i.val v : ℝ)
  have hs : ∑ i : T, μ i.val = 1 := (Finset.sum_coe_sort T μ).trans hμ1
  have hm : ∀ v, ∑ i : T, μ i.val * X i v = p v := by
    intro v
    exact (Finset.sum_coe_sort T (fun z => μ z * (z v : ℝ))).trans (hμp v)
  obtain ⟨a, ν, hν0, hν1, hνp, hb, ht⟩ := finite_affine_support X
    (fun i => (f i.val).untopD 0) p (fun i => μ i.val) (fun i => hμ0 _ i.property) hs hm
  have hab : ∀ z ∈ localSet f p, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0 := by
    intro z hz
    exact hb ⟨z, hz⟩
  refine ⟨a, hab, ?_, ?_⟩
  · apply hull_of_positive_weights X ν p _ hν0 hν1 hνp
    intro i hi
    exact ⟨i.val, ⟨i.property, ht i hi⟩, rfl⟩
  · calc
      affine a p = ∑ i : T, μ i.val * affine a (X i) := (sum_affine a X _ p hs hm).symm
      _ ≤ ∑ i : T, μ i.val * (f i.val).untopD 0 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hμ0 _ i.property))
      _ = ∑ z ∈ localSet f p, μ z * (f z).untopD 0 :=
        Finset.sum_coe_sort T (fun z => μ z * (f z).untopD 0)
      _ ≤ ∑ z ∈ S, lam z * (f z).untopD 0 := hμcost

private lemma ccvOn_subtype_bound (f : (V → ℤ) → WithTop ℝ) (T : Finset (V → ℤ))
    (hT : ∀ z ∈ T, z ∈ DomZ f) (p : V → ℝ) (μ : T → ℝ)
    (h0 : ∀ i, 0 ≤ μ i) (h1 : ∑ i, μ i = 1)
    (hp : ∀ v, ∑ i, μ i * (i.val v : ℝ) = p v) :
    ConvexClosureValOn f T p ≤ ((∑ i : T, μ i * (f i.val).untopD 0 : ℝ) : WithTop ℝ) := by
  let lam : (V → ℤ) → ℝ := fun z => if h : z ∈ T then μ ⟨z, h⟩ else 0
  have hsum (g : (V → ℤ) → ℝ) : ∑ z ∈ T, lam z * g z = ∑ i : T, μ i * g i.val := by
    rw [← Finset.sum_coe_sort T (fun z => lam z * g z)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [lam, dif_pos i.property]
  have hn : ∀ z ∈ T, 0 ≤ lam z := by
    intro z hz
    simpa only [lam, dif_pos hz] using h0 ⟨z, hz⟩
  have hs : ∑ z ∈ T, lam z = 1 := by
    have h := hsum (fun _ => 1)
    simp only [mul_one] at h
    exact h.trans h1
  have hm : ∀ v, ∑ z ∈ T, lam z * (z v : ℝ) = p v := by
    intro v
    exact (hsum (fun z => (z v : ℝ))).trans (hp v)
  have h := ccvOn_le_of f T p lam hn hs hT hm
  rwa [hsum] at h

private lemma local_on_bound (f : (V → ℤ) → WithTop ℝ) (hf : MNat2Convex f)
    (p : V → ℝ) (S : Finset (V → ℤ)) (hS : ∀ z ∈ S, z ∈ DomZ f)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ z ∈ S, 0 ≤ lam z) (h1 : ∑ z ∈ S, lam z = 1)
    (hp : ∀ v, ∑ z ∈ S, lam z * (z v : ℝ) = p v) :
    ConvexClosureValOn f (localSet f p) p ≤
      ((∑ z ∈ S, lam z * (f z).untopD 0 : ℝ) : WithTop ℝ) := by
  obtain ⟨f1, f2, hf1, hf2, rfl⟩ := hf
  let F : (V → ℤ) → WithTop ℝ := fun z => f1 z + f2 z
  have hd1 : ∀ z ∈ S, z ∈ DomZ f1 := by
    intro z hz
    exact (WithTop.add_ne_top.mp (hS z hz)).1
  have hd2 : ∀ z ∈ S, z ∈ DomZ f2 := by
    intro z hz
    exact (WithTop.add_ne_top.mp (hS z hz)).2
  obtain ⟨a1, hb1, hp1, hc1⟩ := local_support f1 hf1 p S hd1 lam h0 h1 hp
  obtain ⟨a2, hb2, hp2, hc2⟩ := local_support f2 hf2 p S hd2 lam h0 h1 hp
  let A1 := tightSet f1 p a1
  let A2 := tightSet f2 p a2
  have hboth := mnat_intersection_hull_mem A1 A2 (tight_mnat f1 hf1 p a1 hb1)
    (tight_mnat f2 hf2 p a2 hb2) p hp1 hp2
  let T := localSet F p
  have hcommon : ∀ z ∈ A1 ∩ A2, z ∈ T := by
    intro z hz
    have h1z := Finset.mem_filter.mp hz.1.1
    have h2z := Finset.mem_filter.mp hz.2.1
    exact Finset.mem_filter.mpr ⟨h1z.1, WithTop.add_ne_top.mpr ⟨h1z.2, h2z.2⟩⟩
  have hinc : IntEmbed (A1 ∩ A2) ⊆ IntEmbed (T : Set (V → ℤ)) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hcommon z hz, rfl⟩
  have hpT := convexHull_mono hinc hboth
  obtain ⟨μ, hμ0, hμ1, hμp⟩ := mix_of_hull_finset T p hpT
  let X : T → V → ℝ := fun i v => (i.val v : ℝ)
  obtain ⟨a, ν, hν0, hν1, hνp, hb, ht⟩ := finite_affine_support X
    (fun i => (F i.val).untopD 0) p μ hμ0 hμ1 hμp
  have hcost : ∑ i : T, ν i * (F i.val).untopD 0 = affine a p := by
    rw [← sum_affine a X ν p hν1 hνp]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < ν i
    · rw [ht i hi]
    · have hz : ν i = 0 := le_antisymm (le_of_not_gt hi) (hν0 i)
      simp [hz]
  have hcompare : affine a p ≤ affine a1 p + affine a2 p := by
    apply affine_compare_hull a a1 a2 (IntEmbed (A1 ∩ A2)) _ p hboth
    rintro _ ⟨z, hz, rfl⟩
    have hbound := hb ⟨z, hcommon z hz⟩
    have hn1 : f1 z ≠ ⊤ := (Finset.mem_filter.mp hz.1.1).2
    have hn2 : f2 z ≠ ⊤ := (Finset.mem_filter.mp hz.2.1).2
    have hval : (F z).untopD 0 = (f1 z).untopD 0 + (f2 z).untopD 0 :=
      WithTop.untopD_add hn1 hn2
    rw [hval, ← hz.1.2, ← hz.2.2] at hbound
    exact hbound
  have htotal : ∑ z ∈ S, lam z * (F z).untopD 0 =
      (∑ z ∈ S, lam z * (f1 z).untopD 0) + (∑ z ∈ S, lam z * (f2 z).untopD 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    change lam z * (f1 z + f2 z).untopD 0 = _
    rw [WithTop.untopD_add (hd1 z hz) (hd2 z hz), mul_add]
  change ConvexClosureValOn F T p ≤ _
  calc
    ConvexClosureValOn F T p ≤ ((∑ i : T, ν i * (F i.val).untopD 0 : ℝ) : WithTop ℝ) :=
      ccvOn_subtype_bound F T (fun z hz => (Finset.mem_filter.mp hz).2) p ν hν0 hν1 hνp
    _ = (affine a p : WithTop ℝ) := by rw [hcost]
    _ ≤ ((affine a1 p + affine a2 p : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.mpr hcompare
    _ ≤ ((∑ z ∈ S, lam z * (F z).untopD 0 : ℝ) : WithTop ℝ) := by
      apply WithTop.coe_le_coe.mpr
      rw [htotal]
      exact add_le_add hc1 hc2

private lemma key (f : (V → ℤ) → WithTop ℝ) (hf : MNat2Convex f)
    (p : V → ℝ) (S : Finset (V → ℤ)) (hS : ∀ z ∈ S, z ∈ DomZ f) :
    ConvexClosureValOn f (localSet f p) p ≤ ConvexClosureValOn f S p := by
  rw [ccvOn_eq f S p]
  obtain hempty | hne := (CCSet f S p).eq_empty_or_nonempty
  · rw [hempty, WithTop.sInf_empty]
    exact le_top
  · apply le_csInf hne
    rintro _ ⟨lam, h0, h1, _, hp, rfl⟩
    exact local_on_bound f hf p S hS lam h0 h1 hp

private lemma function_core (f : (V → ℤ) → WithTop ℝ) (hf : MNat2Convex f) :
    IsIntegrallyConvexFunction f := by
  intro p
  let T := localSet f p
  have hT : ∀ z ∈ T, z ∈ DomZ f := fun z hz => (Finset.mem_filter.mp hz).2
  have hkey := key f hf p
  apply le_antisymm
  · unfold ConvexClosureVal
    apply csInf_le
    · exact ⟨ConvexClosureValOn f T p, by rintro _ ⟨S, hS, rfl⟩; exact hkey S hS⟩
    · exact ⟨T, hT, rfl⟩
  · unfold ConvexClosureVal
    refine le_csInf ⟨ConvexClosureValOn f T p, T, hT, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    exact hkey S hS

end ConjugacyFunctionProof

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MNat2Convex f) : IsIntegrallyConvexFunction f :=
  ConjugacyFunctionProof.function_core f hf
