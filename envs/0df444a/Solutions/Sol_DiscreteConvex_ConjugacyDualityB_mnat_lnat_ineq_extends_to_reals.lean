-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.mnat_lnat_ineq_extends_to_reals
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T04:37:24.195095+00:00
-- url     : https://prove2.me/submissions/40ace145-9907-483c-b900-3b1487507ee4

import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Contrapose
import Theorems.Thm_LP_strong_duality_matrix
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureVal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNatConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntEmbed
import Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_intersection_hull
import Theorems.Thm_DiscreteConvex_LConvexSets_lconvex_intersection_properties

set_option Elab.async false

open scoped BigOperators
open Matrix
open Classical DiscreteConvex.ConjugacyDualityB

-- Affine-support and M-natural lifting machinery reused from our accepted
-- Theorem 8.31 function proof, submission 1e573557-f601-476b-96d3-85ca0d319c53.
namespace InequalityExtensionProof

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

private noncomputable def box (l u : V → ℤ) : Finset (V → ℤ) :=
  Fintype.piFinset fun v => Finset.Icc (l v) (u v)

private lemma mem_box (l u z : V → ℤ) : z ∈ box l u ↔ ∀ v, l v ≤ z v ∧ z v ≤ u v := by
  simp [box, Fintype.mem_piFinset, Finset.mem_Icc]

private noncomputable def boxSet (f : (V → ℤ) → WithTop ℝ) (l u : V → ℤ) :
    Finset (V → ℤ) := (box l u).filter (fun z => z ∈ DomZ f)

private def face (f : (V → ℤ) → WithTop ℝ) (l u : V → ℤ)
    (a : Option V → ℝ) : Set (V → ℤ) :=
  {z | z ∈ boxSet f l u ∧ affine a (fun v => (z v : ℝ)) = (f z).untopD 0}

private lemma move_box_mem (l r : V → ℤ) (x y : Option V → ℤ)
    (hx : (fun v => x (some v)) ∈ box l r)
    (hy : (fun v => y (some v)) ∈ box l r)
    (u v : Option V) (hu : y u < x u) (hv : x v < y v) :
    (fun w => x (some w) - IndicatorVec {u} (some w) + IndicatorVec {v} (some w)) ∈
      box l r := by
  have hxb : inBox l r x := (mem_box _ _ _).mp hx
  have hyb : inBox l r y := (mem_box _ _ _).mp hy
  have h := move_box l r x y hxb hyb u v hu hv
  apply (mem_box _ _ _).mpr
  simpa [inBox, IndicatorVec, DiscreteConvex.MConvexSetsB.CharVec] using h


private lemma face_mnat (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f)
    (l r : V → ℤ) (a : Option V → ℝ)
    (hb : ∀ z ∈ boxSet f l r, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0) :
    MNatConvexSet (face f l r a) := by
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
  have hxN := move_box_mem l r x y (Finset.mem_filter.mp hx.2.1).1
    (Finset.mem_filter.mp hy.2.1).1 u v hu' hv'
  have hyN := move_box_mem l r y x (Finset.mem_filter.mp hy.2.1).1
    (Finset.mem_filter.mp hx.2.1).1 v u hv' hu'
  have hxt : (fun w => x' (some w)) ∈ boxSet f l r := Finset.mem_filter.mpr ⟨hxN, hxfin.2⟩
  have hyt : (fun w => y' (some w)) ∈ boxSet f l r := Finset.mem_filter.mpr ⟨hyN, hyfin.2⟩
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

private def liftL (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {z | (fun v => z (some v) - z none) ∈ D}

private def sectionR : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) where
  toFun p := fun o => o.elim 0 p
  map_add' p q := by funext o; cases o <;> simp
  map_smul' a p := by funext o; cases o <;> simp

private def projectL : (Option V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun p := fun v => p (some v) - p none
  map_add' p q := by funext v; simp; ring
  map_smul' a p := by funext v; simp [mul_sub]

private lemma liftL_hull (D : Set (V → ℤ)) (p : V → ℝ)
    (hp : p ∈ convexHull ℝ (IntEmbed D)) :
    sectionR p ∈ DiscreteConvex.LConvexSets.ConvexClosureSet (liftL D) := by
  have hi : sectionR '' IntEmbed D ⊆
      (fun z : Option V → ℤ => fun o => (z o : ℝ)) '' liftL D := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨fun o => o.elim 0 z, ?_, ?_⟩
    · simpa [liftL] using hz
    · funext o; cases o <;> simp [sectionR]
  apply convexHull_mono hi
  rw [← LinearMap.image_convexHull]
  exact ⟨p, hp, rfl⟩

private lemma lnat_intersection_hull_mem (D1 D2 : Set (V → ℤ))
    (h1 : DiscreteConvex.LConvexSets.LConvexSet (liftL D1))
    (h2 : DiscreteConvex.LConvexSets.LConvexSet (liftL D2)) (p : V → ℝ)
    (hp1 : p ∈ convexHull ℝ (IntEmbed D1))
    (hp2 : p ∈ convexHull ℝ (IntEmbed D2)) :
    p ∈ convexHull ℝ (IntEmbed (D1 ∩ D2)) := by
  have hboth : sectionR p ∈ DiscreteConvex.LConvexSets.ConvexClosureSet
      (liftL D1 ∩ liftL D2) := by
    rw [← (DiscreteConvex.LConvexSets.lconvex_intersection_properties _ _ h1 h2).1]
    exact ⟨liftL_hull D1 p hp1, liftL_hull D2 p hp2⟩
  have hi : projectL '' ((fun z : Option V → ℤ => fun o => (z o : ℝ)) ''
      (liftL D1 ∩ liftL D2)) ⊆ IntEmbed (D1 ∩ D2) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨fun v => z (some v) - z none, ⟨hz.1, hz.2⟩, ?_⟩
    funext v
    simp [projectL]
  apply convexHull_mono hi
  rw [← LinearMap.image_convexHull]
  exact ⟨sectionR p, hboth, by funext v; simp [projectL, sectionR]⟩

private lemma face_lnat (f : (V → ℤ) → WithTop ℝ) (hf : LNaturalConvex f)
    (l r : V → ℤ) (a : Option V → ℝ)
    (hb : ∀ z ∈ boxSet f l r, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0) :
    DiscreteConvex.LConvexSets.LConvexSet (liftL (face f l r a)) := by
  constructor
  · intro x hx y hy
    let dx : V → ℤ := fun v => x (some v) - x none
    let dy : V → ℤ := fun v => y (some v) - y none
    let dz : V → ℤ := fun v => (x ⊔ y) (some v) - (x ⊔ y) none
    let dw : V → ℤ := fun v => (x ⊓ y) (some v) - (x ⊓ y) none
    change dx ∈ face f l r a at hx
    change dy ∈ face f l r a at hy
    have hxf : f dx ≠ ⊤ := (Finset.mem_filter.mp hx.1).2
    have hyf : f dy ≠ ⊤ := (Finset.mem_filter.mp hy.1).2
    have hineq : f dz + f dw ≤ f dx + f dy := hf.1 x y
    have hfin := WithTop.add_ne_top.mp
      (ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hxf, hyf⟩) hineq)
    have hxb := (mem_box _ _ _).mp (Finset.mem_filter.mp hx.1).1
    have hyb := (mem_box _ _ _).mp (Finset.mem_filter.mp hy.1).1
    have hzb : dz ∈ box l r := by
      apply (mem_box _ _ _).mpr
      intro v
      have hxv := hxb v
      have hyv := hyb v
      dsimp [dx, dy] at hxv hyv
      dsimp [dz]
      change l v ≤ max (x (some v)) (y (some v)) - max (x none) (y none) ∧
        max (x (some v)) (y (some v)) - max (x none) (y none) ≤ r v
      omega
    have hwb : dw ∈ box l r := by
      apply (mem_box _ _ _).mpr
      intro v
      have hxv := hxb v
      have hyv := hyb v
      dsimp [dx, dy] at hxv hyv
      dsimp [dw]
      change l v ≤ min (x (some v)) (y (some v)) - min (x none) (y none) ∧
        min (x (some v)) (y (some v)) - min (x none) (y none) ≤ r v
      omega
    have hzS : dz ∈ boxSet f l r := Finset.mem_filter.mpr ⟨hzb, hfin.1⟩
    have hwS : dw ∈ boxSet f l r := Finset.mem_filter.mpr ⟨hwb, hfin.2⟩
    have hreal := real_add_le hfin.1 hfin.2 hxf hyf hineq
    have hpair : affine a (fun v => (dz v : ℝ)) + affine a (fun v => (dw v : ℝ)) =
        affine a (fun v => (dx v : ℝ)) + affine a (fun v => (dy v : ℝ)) := by
      apply affine_pair
      intro v
      have heq : dz v + dw v = dx v + dy v := by
        dsimp [dz, dw, dx, dy]
        change max (x (some v)) (y (some v)) - max (x none) (y none) +
          (min (x (some v)) (y (some v)) - min (x none) (y none)) = _
        omega
      exact_mod_cast heq
    have hzE : affine a (fun v => (dz v : ℝ)) = (f dz).untopD 0 := by
      have hbz := hb _ hzS
      have hbw := hb _ hwS
      have hxe := hx.2
      have hye := hy.2
      linarith
    have hwE : affine a (fun v => (dw v : ℝ)) = (f dw).untopD 0 := by
      have hbz := hb _ hzS
      have hbw := hb _ hwS
      have hxe := hx.2
      have hye := hy.2
      linarith
    exact ⟨⟨hzS, hzE⟩, ⟨hwS, hwE⟩⟩
  · intro x hx
    change (fun v => x (some v) - x none) ∈ face f l r a at hx
    constructor
    · change (fun v => (x (some v) + 1) - (x none + 1)) ∈ face f l r a
      simpa only [add_sub_add_right_eq_sub] using hx
    · change (fun v => (x (some v) - 1) - (x none - 1)) ∈ face f l r a
      simpa only [sub_sub_sub_cancel_right] using hx

private def Rep (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ))
    (p : V → ℝ) (lam : (V → ℤ) → ℝ) : Prop :=
  (∀ z ∈ S, 0 ≤ lam z) ∧ (∑ z ∈ S, lam z = 1) ∧
  (∀ z ∈ S, z ∈ DomZ f) ∧ (∀ v, ∑ z ∈ S, lam z * (z v : ℝ) = p v)

private def cost (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ))
    (lam : (V → ℤ) → ℝ) : ℝ := ∑ z ∈ S, lam z * (f z).untopD 0

private lemma box_support (f : (V → ℤ) → WithTop ℝ) (l r : V → ℤ)
    (p : V → ℝ) (S : Finset (V → ℤ)) (lam : (V → ℤ) → ℝ)
    (hr : Rep f S p lam) (hbox : ∀ z ∈ S, z ∈ box l r) :
    ∃ a : Option V → ℝ,
      (∀ z ∈ boxSet f l r, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0) ∧
      p ∈ convexHull ℝ (IntEmbed (face f l r a)) ∧
      affine a p ≤ cost f S lam := by
  let T := boxSet f l r
  have hST : ∀ z ∈ S, z ∈ T := fun z hz => Finset.mem_filter.mpr ⟨hbox z hz, hr.2.2.1 z hz⟩
  have hs : ∑ i : S, lam i.val = 1 := (Finset.sum_coe_sort S lam).trans hr.2.1
  have hm : ∀ v, ∑ i : S, lam i.val * (i.val v : ℝ) = p v := by
    intro v
    exact (Finset.sum_coe_sort S (fun z => lam z * (z v : ℝ))).trans (hr.2.2.2 v)
  have hpT : p ∈ convexHull ℝ (IntEmbed (T : Set (V → ℤ))) := by
    apply hull_of_positive_weights (fun i : S => fun v => (i.val v : ℝ))
      (fun i => lam i.val) p _ (fun i => hr.1 _ i.property) hs hm
    intro i _
    exact ⟨i.val, hST _ i.property, rfl⟩
  obtain ⟨μ, hμ0, hμ1, hμp⟩ := mix_of_hull_finset T p hpT
  let X : T → V → ℝ := fun i v => (i.val v : ℝ)
  obtain ⟨a, ν, hν0, hν1, hνp, hb, ht⟩ := finite_affine_support X
    (fun i => (f i.val).untopD 0) p μ hμ0 hμ1 hμp
  have hab : ∀ z ∈ T, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0 := by
    intro z hz
    exact hb ⟨z, hz⟩
  refine ⟨a, hab, ?_, ?_⟩
  · apply hull_of_positive_weights X ν p _ hν0 hν1 hνp
    intro i hi
    exact ⟨i.val, ⟨i.property, ht i hi⟩, rfl⟩
  · calc
      affine a p = ∑ i : S, lam i.val * affine a (fun v => (i.val v : ℝ)) :=
        (sum_affine a _ _ p hs hm).symm
      _ ≤ ∑ i : S, lam i.val * (f i.val).untopD 0 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (hab _ (hST _ i.property)) (hr.1 _ i.property))
      _ = cost f S lam := Finset.sum_coe_sort S (fun z => lam z * (f z).untopD 0)

private lemma affine_nonneg_hull (a b : Option V → ℝ) (D : Set (V → ℤ))
    (h : ∀ z ∈ D, 0 ≤ affine a (fun v => (z v : ℝ)) + affine b (fun v => (z v : ℝ)))
    (p : V → ℝ) (hp : p ∈ convexHull ℝ (IntEmbed D)) :
    0 ≤ affine a p + affine b p := by
  have h' : affine (fun _ => 0) p ≤ affine a p + affine b p := by
    apply affine_compare_hull _ a b (IntEmbed D) _ p hp
    rintro _ ⟨z, hz, rfl⟩
    simpa [affine] using h z hz
  simpa [affine] using h'

private lemma paired_cost (f g : (V → ℤ) → WithTop ℝ)
    (hge : ∀ z, 0 ≤ f z + g z)
    (hfaces : ∀ (l r : V → ℤ) (a b : Option V → ℝ),
      (∀ z ∈ boxSet f l r, affine a (fun v => (z v : ℝ)) ≤ (f z).untopD 0) →
      (∀ z ∈ boxSet g l r, affine b (fun v => (z v : ℝ)) ≤ (g z).untopD 0) →
      ∀ p, p ∈ convexHull ℝ (IntEmbed (face f l r a)) →
        p ∈ convexHull ℝ (IntEmbed (face g l r b)) →
        p ∈ convexHull ℝ (IntEmbed (face f l r a ∩ face g l r b)))
    (p : V → ℝ) (S T : Finset (V → ℤ)) (lam mu : (V → ℤ) → ℝ)
    (hS : Rep f S p lam) (hT : Rep g T p mu) :
    0 ≤ cost f S lam + cost g T mu := by
  let r : V → ℤ := fun v => ∑ z ∈ S ∪ T, |z v|
  let l : V → ℤ := fun v => -r v
  have hbox : ∀ z ∈ S ∪ T, z ∈ box l r := by
    intro z hz
    apply (mem_box _ _ _).mpr
    intro v
    have habs : |z v| ≤ r v := Finset.single_le_sum (fun y _ => abs_nonneg (y v)) hz
    exact abs_le.mp habs
  obtain ⟨a, hba, hpa, hca⟩ := box_support f l r p S lam hS
    (fun z hz => hbox z (Finset.mem_union_left T hz))
  obtain ⟨b, hbb, hpb, hcb⟩ := box_support g l r p T mu hT
    (fun z hz => hbox z (Finset.mem_union_right S hz))
  have hp := hfaces l r a b hba hbb p hpa hpb
  have hn : 0 ≤ affine a p + affine b p := by
    apply affine_nonneg_hull a b _ _ p hp
    intro z hz
    have hfz : f z ≠ ⊤ := (Finset.mem_filter.mp hz.1.1).2
    have hgz : g z ≠ ⊤ := (Finset.mem_filter.mp hz.2.1).2
    have hv : (0 : ℝ) ≤ (f z).untopD 0 + (g z).untopD 0 := by
      apply WithTop.coe_le_coe.mp
      simpa only [WithTop.coe_add, coe_value hfz, coe_value hgz, WithTop.coe_zero] using hge z
    rwa [← hz.1.2, ← hz.2.2] at hv
  linarith

-- Taking lower bounds of the two nested infima requires no boundedness
-- assumption on the whole function and also covers empty representations.
private lemma closure_ge (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (c : ℝ)
    (h : ∀ S lam, Rep f S p lam → c ≤ cost f S lam) :
    (c : WithTop ℝ) ≤ ConvexClosureVal f p := by
  unfold ConvexClosureVal
  apply le_csInf
  · exact ⟨ConvexClosureValOn f ∅ p, ∅, by simp, rfl⟩
  · rintro _ ⟨S, hS, rfl⟩
    unfold ConvexClosureValOn
    by_cases he : {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
      (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) ∧
      L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)} = ∅
    · rw [he, WithTop.sInf_empty]
      exact le_top
    · apply le_csInf (Set.nonempty_iff_ne_empty.mpr he)
      rintro _ ⟨lam, h0, h1, hd, hp, rfl⟩
      exact WithTop.coe_le_coe.mpr (h S lam ⟨h0, h1, hd, hp⟩)

private lemma closure_pair_nonneg (f g : (V → ℤ) → WithTop ℝ)
    (h : ∀ p S T lam mu, Rep f S p lam → Rep g T p mu →
      0 ≤ cost f S lam + cost g T mu) :
    ∀ p, 0 ≤ ConvexClosureVal f p + ConvexClosureVal g p := by
  intro p
  by_cases hf : ConvexClosureVal f p = ⊤
  · simp [hf]
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hf
    have hga : ((-a : ℝ) : WithTop ℝ) ≤ ConvexClosureVal g p := by
      apply closure_ge
      intro T mu hT
      have hfa : ((-cost g T mu : ℝ) : WithTop ℝ) ≤ ConvexClosureVal f p := by
        apply closure_ge
        intro S lam hS
        have hc := h p S T lam mu hS hT
        linarith
      rw [← ha] at hfa
      have hr := WithTop.coe_le_coe.mp hfa
      linarith
    calc
      0 = (a : WithTop ℝ) + ((-a : ℝ) : WithTop ℝ) := by simp [← WithTop.coe_add]
      _ ≤ ConvexClosureVal f p + ConvexClosureVal g p := add_le_add (le_of_eq ha) hga

end InequalityExtensionProof

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f h2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f → MNaturalConvex h2 →
      (∀ x : V → ℤ, f x + h2 x ≥ 0) →
      ∀ x : V → ℝ, ConvexClosureVal f x + ConvexClosureVal h2 x ≥ 0) ∧
    (∀ g k2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g → LNaturalConvex k2 →
      (∀ p : V → ℤ, g p + k2 p ≥ 0) →
      ∀ p : V → ℝ, ConvexClosureVal g p + ConvexClosureVal k2 p ≥ 0) := by
  constructor
  · intro f g hf hg hge
    apply InequalityExtensionProof.closure_pair_nonneg f g
    apply InequalityExtensionProof.paired_cost f g hge
    intro l r a b hb1 hb2 p hp1 hp2
    exact InequalityExtensionProof.mnat_intersection_hull_mem _ _
      (InequalityExtensionProof.face_mnat f hf l r a hb1)
      (InequalityExtensionProof.face_mnat g hg l r b hb2) p hp1 hp2
  · intro f g hf hg hge
    apply InequalityExtensionProof.closure_pair_nonneg f g
    apply InequalityExtensionProof.paired_cost f g hge
    intro l r a b hb1 hb2 p hp1 hp2
    exact InequalityExtensionProof.lnat_intersection_hull_mem _ _
      (InequalityExtensionProof.face_lnat f hf l r a hb1)
      (InequalityExtensionProof.face_lnat g hg l r b hb2) p hp1 hp2
