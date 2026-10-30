-- Prove2me | solution 1 for BirkhoffGlobalSection.strict_convex_orbit_positive_canonical_model
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:50:49.21414+00:00
-- url     : https://prove2.me/submissions/d26c4d42-28d5-4005-a777-d61aaf61f0e3

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_canonical_model_frame_data
import Theorems.Thm_HryniewiczCriterion_local_positive_canonical_differential


set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.CanonicalCoordinates
open BirkhoffGlobalSection HryniewiczCriterion
open scoped ContDiff
noncomputable section
def toHrynCLM : Phase →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 2,
      ContinuousLinearMap.proj 1, -ContinuousLinearMap.proj 3] i

def fromHrynCLM : R4 →L[ℝ] Phase :=
  ContinuousLinearMap.pi fun i =>
    ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 2,
      -ContinuousLinearMap.proj 1, -ContinuousLinearMap.proj 3] i

lemma toHrynCLM_apply (v : Phase) : toHrynCLM v = toHryn v := by
  ext i; fin_cases i <;> simp [toHrynCLM, toHryn]
lemma fromHrynCLM_apply (v : R4) : fromHrynCLM v = fromHryn v := by
  ext i; fin_cases i <;> simp [fromHrynCLM, fromHryn]

lemma from_to (v : Phase) : fromHryn (toHryn v) = v := by
  ext i; fin_cases i <;> simp [fromHryn, toHryn]
lemma to_from (v : R4) : toHryn (fromHryn v) = v := by
  ext i; fin_cases i <;> simp [fromHryn, toHryn]


def coordinateEquiv : Phase ≃L[ℝ] R4 where
  toLinearEquiv := { toHrynCLM.toLinearMap with
    invFun := fromHrynCLM
    left_inv := by
      intro v
      change fromHrynCLM (toHrynCLM v) = v
      rw [toHrynCLM_apply, fromHrynCLM_apply, from_to]
    right_inv := by
      intro v
      change toHrynCLM (fromHrynCLM v) = v
      rw [fromHrynCLM_apply, toHrynCLM_apply, to_from] }
  continuous_toFun := toHrynCLM.continuous
  continuous_invFun := fromHrynCLM.continuous

lemma coordinateEquiv_apply (v : Phase) : coordinateEquiv v = toHryn v := toHrynCLM_apply v
lemma coordinateEquiv_symm_apply (v : R4) : coordinateEquiv.symm v = fromHryn v :=
  fromHrynCLM_apply v

lemma coordinateEquiv_coe : (coordinateEquiv : Phase →L[ℝ] R4) = toHrynCLM := by
  ext v i; rfl
lemma coordinateEquiv_symm_coe : (coordinateEquiv.symm : R4 →L[ℝ] Phase) = fromHrynCLM := by
  ext v i; rfl

lemma pullback_fderiv (G : Phase → ℝ) (y : R4) :
    fderiv ℝ (fun z => G (fromHryn z)) y =
      (fderiv ℝ G (fromHryn y)).comp fromHrynCLM := by
  have h := coordinateEquiv.symm.comp_right_fderiv (f := G) (x := y)
  simpa only [Function.comp_def, coordinateEquiv_symm_apply, coordinateEquiv_symm_coe] using h

lemma fromHrynCLM_single (i : Fin 4) :
    fromHrynCLM (Pi.single i 1) =
      ![Pi.single 0 1, -Pi.single 2 1, Pi.single 1 1, -Pi.single 3 1] i := by
  ext j; fin_cases i <;> fin_cases j <;> simp [fromHrynCLM, Pi.single_apply]

lemma vector_field_conjugacy (G : Phase → ℝ) (y : R4) :
    HryniewiczCriterion.hamiltonianVectorField (fun z => G (fromHryn z)) y =
      toHrynCLM (BirkhoffGlobalSection.hamiltonianVectorField G (fromHryn y)) := by
  have hbasis : ∀ i : Fin 4, coordinateVector i = Pi.single i 1 := by
    intro i; ext j; simp [coordinateVector, Pi.single_apply, eq_comm]
  ext i; fin_cases i <;>
    simp [HryniewiczCriterion.hamiltonianVectorField, HryniewiczCriterion.partialDeriv,
      BirkhoffGlobalSection.hamiltonianVectorField, BirkhoffGlobalSection.partialDerivative,
      pullback_fderiv, fromHrynCLM_single, toHrynCLM, hbasis]

lemma fderiv_vector_field_conjugacy (G : Phase → ℝ) (y : R4) :
    fderiv ℝ (HryniewiczCriterion.hamiltonianVectorField (fun z => G (fromHryn z))) y =
      toHrynCLM.comp ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G)
        (fromHryn y)).comp fromHrynCLM) := by
  have heq : HryniewiczCriterion.hamiltonianVectorField (fun z => G (fromHryn z)) =
      coordinateEquiv ∘ BirkhoffGlobalSection.hamiltonianVectorField G ∘ coordinateEquiv.symm := by
    funext z
    simpa only [Function.comp_apply, coordinateEquiv_apply, coordinateEquiv_symm_apply,
      toHrynCLM_apply] using vector_field_conjugacy G z
  rw [heq, coordinateEquiv.comp_fderiv, coordinateEquiv.symm.comp_right_fderiv]
  simp only [coordinateEquiv_coe, coordinateEquiv_symm_coe, coordinateEquiv_symm_apply]


noncomputable def transformedFlow (Y : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) : R4 →L[ℝ] R4 :=
  toHrynCLM.comp ((Y t).comp fromHrynCLM)

lemma transformed_trajectory (G : Phase → ℝ) (x : ℝ → Phase)
    (hx : ∀ t, HasDerivAt x (BirkhoffGlobalSection.hamiltonianVectorField G (x t)) t) :
    ∀ t, HasDerivAt (fun s => toHryn (x s))
      (HryniewiczCriterion.hamiltonianVectorField (fun y => G (fromHryn y)) (toHryn (x t))) t := by
  intro t
  have h := toHrynCLM.hasFDerivAt.comp_hasDerivAt t (hx t)
  simpa only [Function.comp_def, vector_field_conjugacy, toHrynCLM_apply, from_to] using h

lemma transformed_linearized_flow (G : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    IsLinearizedFlow (fun y => G (fromHryn y)) (fun t => toHryn (x t)) (transformedFlow Y) := by
  have hid : fromHrynCLM.comp toHrynCLM = ContinuousLinearMap.id ℝ Phase := by
    ext v i
    change fromHrynCLM (toHrynCLM v) i = v i
    simp only [toHrynCLM_apply, fromHrynCLM_apply, from_to]
  have hid' : toHrynCLM.comp fromHrynCLM = ContinuousLinearMap.id ℝ R4 := by
    ext v i
    change toHrynCLM (fromHrynCLM v) i = v i
    simp only [fromHrynCLM_apply, toHrynCLM_apply, to_from]
  refine ⟨?_, ?_⟩
  · simp only [transformedFlow, hY0, ContinuousLinearMap.id_comp, hid']
  · intro t
    change HasDerivAt (fun s => transformedFlow Y s) _ t
    have h := (hasDerivAt_const t toHrynCLM).clm_comp
      ((hY t).clm_comp (hasDerivAt_const t fromHrynCLM))
    simpa only [transformedFlow, fderiv_vector_field_conjugacy, from_to,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, zero_add, add_zero,
      ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc fromHrynCLM toHrynCLM,
      hid, ContinuousLinearMap.id_comp] using h

lemma transformedFlow_matrix (Y : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) :
    LinearMap.toMatrix' (transformedFlow Y t : R4 →ₗ[ℝ] R4) = hrynFlowMatrix Y t := by
  ext i j
  change toHrynCLM (Y t (fromHrynCLM (Pi.single j 1))) i =
    toHryn (Y t (fromHryn (Pi.single j 1))) i
  rw [toHrynCLM_apply, fromHrynCLM_apply]

lemma pullback_contDiffAt (G : Phase → ℝ) (y : R4)
    (hG : ContDiffAt ℝ 2 G (fromHryn y)) :
    ContDiffAt ℝ 2 (fun z => G (fromHryn z)) y := by
  have hGc : ContDiffAt ℝ 2 G (coordinateEquiv.symm y) := by
    simpa only [coordinateEquiv_symm_apply] using hG
  have h := hGc.comp y coordinateEquiv.symm.contDiff.contDiffAt
  simpa only [Function.comp_def, coordinateEquiv_symm_apply] using h


lemma pullback_hessian (G : Phase → ℝ) (y v w : R4)
    (hG : ContDiffAt ℝ 2 G (fromHryn y)) :
    fderiv ℝ (fderiv ℝ (fun z => G (fromHryn z))) y v w =
      fderiv ℝ (fderiv ℝ G) (fromHryn y) (fromHryn v) (fromHryn w) := by
  have hdH : DifferentiableAt ℝ (fderiv ℝ (fun z => G (fromHryn z))) y :=
    ((pullback_contDiffAt G y hG).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdG : DifferentiableAt ℝ (fderiv ℝ G) (fromHryn y) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp y hdH.hasFDerivAt
  have hdGc : DifferentiableAt ℝ (fderiv ℝ G) (fromHrynCLM y) := by
    simpa only [fromHrynCLM_apply] using hdG
  have h2 := ((ContinuousLinearMap.apply ℝ ℝ (fromHryn w)).hasFDerivAt.comp
    (fromHrynCLM y) hdGc.hasFDerivAt).comp y fromHrynCLM.hasFDerivAt
  have h2' := h2.congr_of_eventuallyEq
    (f₁ := fun z => fderiv ℝ (fun z => G (fromHryn z)) z w)
    (Filter.Eventually.of_forall fun z => by
      simp only [Function.comp_apply, pullback_fderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, fromHrynCLM_apply])
  have he := congrArg (fun L : R4 →L[ℝ] ℝ => L v) (h1.unique h2')
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, fromHrynCLM_apply] using he

lemma directional_hessian_eq (G : Phase → ℝ) (y v w : Phase)
    (hG : ContDiffAt ℝ 2 G y) :
    fderiv ℝ (fun z => fderiv ℝ G z w) y v = fderiv ℝ (fderiv ℝ G) y v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp y hd.hasFDerivAt
  have he := congrArg (fun L : Phase →L[ℝ] ℝ => L v) h.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using he

end
end BirkhoffGlobalSection.CanonicalCoordinates

open BirkhoffGlobalSection HryniewiczCriterion BirkhoffGlobalSection.CanonicalCoordinates
open scoped ContDiff

theorem solution (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    IsPositiveMovingFrame (canonicalRadialFrame G x) (canonicalTransversePath G x T Y) T := by
  let H : R4 → ℝ := fun y => G (fromHryn y)
  let y : ℝ → R4 := fun t => toHryn (x t)
  let V := transformedFlow Y
  have hG : ∀ t, ContDiffAt ℝ 2 G (x t) := fun t => (hx.2.1 t).1.1 _ (by simp)
  have hH : ∀ t, ContDiffAt ℝ 2 H (y t) := by
    intro t
    apply pullback_contDiffAt
    simpa only [y, from_to] using hG t
  have hxH : ∀ t, HasDerivAt y (HryniewiczCriterion.hamiltonianVectorField H (y t)) t :=
    transformed_trajectory G x hx.2.2.1
  have hVH : IsLinearizedFlow H y V := transformed_linearized_flow G x Y hY0 hY
  have hrH : ∀ t, 0 < fderiv ℝ H (y t) (y t) := by
    intro t
    change 0 < fderiv ℝ (fun z => G (fromHryn z)) (toHryn (x t)) (toHryn (x t))
    rw [pullback_fderiv]
    simpa only [ContinuousLinearMap.comp_apply, fromHrynCLM_apply, from_to] using (hx.2.1 t).2
  have hBH : ∀ t v, fderiv ℝ H (y t) v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) (y t) v v := by
    intro t v hv hvne
    have hvne' : fromHryn v ≠ 0 := by
      intro he
      apply hvne
      apply coordinateEquiv.symm.injective
      rw [map_zero, coordinateEquiv_symm_apply]
      exact he
    have hvtan : fderiv ℝ G (x t) (fromHryn v) = 0 := by
      simpa only [H, y, pullback_fderiv, ContinuousLinearMap.comp_apply,
        fromHrynCLM_apply, from_to] using hv
    have hp := (hx.2.1 t).1.2 (x t) (by simp) (fromHryn v) hvne' hvtan
    rw [directional_hessian_eq G (x t) (fromHryn v) (fromHryn v) (hG t)] at hp
    have he := pullback_hessian G (toHryn (x t)) v v (by simpa only [from_to] using hG t)
    simp only [from_to] at he
    change 0 < fderiv ℝ (fderiv ℝ (fun z => G (fromHryn z))) (toHryn (x t)) v v
    rw [he]
    exact hp
  obtain ⟨hsp, hhalf, hcont, hend, hφc, hφ0⟩ := canonical_model_frame_data G x T hx Y hY0 hY
  have hdiff := HryniewiczCriterion.local_positive_canonical_differential H y T hx.1.ne' hH hxH hrH hBH V hVH hsp
  have hdiff' :
      (∀ τ, Matrix.det (fun i j => canonicalTransversePath G x T Y τ i j) = 1) ∧
      (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ,
        (∀ i j, Continuous fun t => S t i j) ∧ (∀ t, (S t).PosDef) ∧
        ∀ t i j, HasDerivAt
          (fun s => ((canonicalRadialFrame G x 0)⁻¹ * canonicalRadialFrame G x s *
            blockOne (fun i j => canonicalTransversePath G x T Y (s / T) i j)) i j)
          ((symplJ4 * S t * ((canonicalRadialFrame G x 0)⁻¹ * canonicalRadialFrame G x t *
            blockOne (fun i j => canonicalTransversePath G x T Y (t / T) i j))) i j) t) := by
    simpa only [H, y, V, transformedFlow_matrix, canonicalRadialFrame,
      canonicalTransversePath] using hdiff
  exact ⟨hsp, hhalf, hcont, hend, hφc, (fun τ _ => hdiff'.1 τ), hφ0, hdiff'.2⟩
