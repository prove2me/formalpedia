-- Prove2me | solution 1 for ChanceStateCtrl.PDE.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:35:18.692757+00:00
-- url     : https://prove2.me/submissions/11ee34ec-3fc9-44eb-b250-8eec7cbfb45d

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace Aux_ChanceStateCtrl_PDE_lemma_2_9

lemma bdd {X : Type*} [TopologicalSpace X] [CompactSpace X] (F : C(X, ℝ)) :
    BddAbove (Set.range (fun x => F x)) :=
  ⟨‖F‖, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (by simpa using F.norm_coe_le_norm x)⟩

lemma sup_le_add {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (F G : C(X, ℝ)) : (⨆ x, F x) ≤ (⨆ x, G x) + ‖F - G‖ := by
  apply ciSup_le
  intro x
  have h1 : F x = G x + (F - G) x := by simp
  have h2 : (F - G) x ≤ ‖F - G‖ :=
    (le_abs_self _).trans (by simpa using (F - G).norm_coe_le_norm x)
  have h3 : G x ≤ ⨆ x, G x := le_ciSup (bdd G) x
  linarith

lemma sup_comb {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (F G : C(X, ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (⨆ x, (a * F x + b * G x)) ≤ a * (⨆ x, F x) + b * (⨆ x, G x) := by
  apply ciSup_le
  intro x
  exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (bdd F) x) ha)
    (mul_le_mul_of_nonneg_left (le_ciSup (bdd G) x) hb)

end Aux_ChanceStateCtrl_PDE_lemma_2_9

open Aux_ChanceStateCtrl_PDE_lemma_2_9 in
open ChanceStateCtrl.PDE in
theorem solution {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ) :
    ConvexOn ℝ Set.univ (Function.uncurry (gPDE Ainv f₀ φ α)) ∧
    (∃ C, LipschitzWith C (Function.uncurry (gPDE Ainv f₀ φ α))) ∧
    ∀ u : L2 D, MeasurableSet {w | gPDE Ainv f₀ φ α u (ξ w) ≤ 0} ∧
      {w | gPDE Ainv f₀ φ α u (ξ w) ≤ 0} =
        {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ u (ξ w) x ≤ α} := by
  obtain ⟨x0, hx0⟩ := hDne
  haveI : Nonempty (closure D) := ⟨⟨x0, subset_closure hx0⟩⟩
  set Lin : (L2 D × EuclideanSpace ℝ (Fin m)) →L[ℝ] L2 D :=
    ContinuousLinearMap.fst ℝ _ _ + ∑ i, ((EuclideanSpace.proj i).comp
      (ContinuousLinearMap.snd ℝ (L2 D) (EuclideanSpace ℝ (Fin m)))).smulRight (φ i) with hLindef
  have hLin : ∀ w : L2 D × EuclideanSpace ℝ (Fin m), Lin w = w.1 + ∑ i, w.2 i • φ i := by
    intro w
    simp [hLindef, ContinuousLinearMap.sum_apply]
  have hS : ∀ w : L2 D × EuclideanSpace ℝ (Fin m),
      stateS Ainv f₀ φ w.1 w.2 = Ainv (Lin w + f₀) := by
    intro w
    unfold stateS
    rw [hLin]
    congr 1
    abel
  have hg : ∀ w : L2 D × EuclideanSpace ℝ (Fin m),
      Function.uncurry (gPDE Ainv f₀ φ α) w = (⨆ x, Ainv (Lin w + f₀) x) - α := by
    intro w
    show gPDE Ainv f₀ φ α w.1 w.2 = _
    unfold gPDE
    rw [hS w]
  have hLipW : LipschitzWith (‖Ainv‖₊ * ‖Lin‖₊) (Function.uncurry (gPDE Ainv f₀ φ α)) := by
    refine LipschitzWith.of_dist_le_mul (fun w1 w2 => ?_)
    rw [hg, hg, Real.dist_eq]
    have hdiff : Ainv (Lin w1 + f₀) - Ainv (Lin w2 + f₀) = Ainv (Lin (w1 - w2)) := by
      rw [map_sub Lin, ← map_sub Ainv]
      congr 1
      abel
    have h1 := sup_le_add (Ainv (Lin w1 + f₀)) (Ainv (Lin w2 + f₀))
    have h2 := sup_le_add (Ainv (Lin w2 + f₀)) (Ainv (Lin w1 + f₀))
    rw [hdiff] at h1
    rw [← norm_neg, neg_sub, hdiff] at h2
    have h3 : ‖Ainv (Lin (w1 - w2))‖ ≤ ‖Ainv‖ * ‖Lin‖ * dist w1 w2 := by
      rw [dist_eq_norm]
      calc ‖Ainv (Lin (w1 - w2))‖ ≤ ‖Ainv‖ * ‖Lin (w1 - w2)‖ := Ainv.le_opNorm _
        _ ≤ ‖Ainv‖ * (‖Lin‖ * ‖w1 - w2‖) :=
            mul_le_mul_of_nonneg_left (Lin.le_opNorm _) (norm_nonneg Ainv)
        _ = ‖Ainv‖ * ‖Lin‖ * ‖w1 - w2‖ := by ring
    push_cast
    rw [abs_le]
    constructor <;> linarith
  refine ⟨⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro w1 _ w2 _ a b ha hb hab
    rw [hg, hg, hg, smul_eq_mul, smul_eq_mul]
    have e : Ainv (Lin (a • w1 + b • w2) + f₀) =
        a • Ainv (Lin w1 + f₀) + b • Ainv (Lin w2 + f₀) := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      rw [map_add, map_smul, map_smul, smul_add, smul_add]
      have : f₀ = a • f₀ + b • f₀ := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      abel
    rw [e]
    have := sup_comb (Ainv (Lin w1 + f₀)) (Ainv (Lin w2 + f₀)) a b ha hb
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    have hα : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
    linarith
  · exact ⟨_, hLipW⟩
  · intro u
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin m) => gPDE Ainv f₀ φ α u z) := by
      have hfun : (fun z : EuclideanSpace ℝ (Fin m) => gPDE Ainv f₀ φ α u z) =
          Function.uncurry (gPDE Ainv f₀ φ α) ∘ Prod.mk u := rfl
      rw [hfun]
      exact (hLipW.comp (LipschitzWith.prodMk_left u)).continuous
    have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin m) | gPDE Ainv f₀ φ α u z ≤ 0} :=
      isClosed_le hcont continuous_const
    have hms : MeasurableSet {z : EuclideanSpace ℝ (Fin m) | gPDE Ainv f₀ φ α u z ≤ 0} :=
      hclosed.measurableSet
    refine ⟨measurableSet_preimage hξ hms, ?_⟩
    ext w
    simp only [Set.mem_setOf_eq]
    set F := stateS Ainv f₀ φ u (ξ w) with hF
    have hgF : gPDE Ainv f₀ φ α u (ξ w) = (⨆ x, F x) - α := rfl
    rw [hgF, sub_nonpos, ciSup_le_iff (bdd F)]
    constructor
    · intro h x _
      exact h x
    · intro h x
      set A : Set (closure D) := {y | y.1 ∈ D} with hAdef
      have hdense : closure A = Set.univ := by
        rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
        have himg : (Subtype.val '' A) = D := by
          ext y
          simp only [Set.mem_image, hAdef, Set.mem_setOf_eq]
          constructor
          · rintro ⟨y', hy', rfl⟩; exact hy'
          · intro hy; exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
        rw [himg]
        ext y
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        exact y.2
      have hC : IsClosed {y : closure D | F y ≤ α} := isClosed_le F.continuous continuous_const
      have hsub : closure A ⊆ {y : closure D | F y ≤ α} :=
        closure_minimal (fun y hy => h y hy) hC
      exact hsub (hdense ▸ Set.mem_univ x)
