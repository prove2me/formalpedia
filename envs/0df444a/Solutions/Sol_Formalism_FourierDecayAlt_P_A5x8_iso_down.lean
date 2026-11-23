-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_down
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.264554+00:00
-- url     : https://prove2.me/submissions/00df0f3d-8f42-4115-b3c6-8369e81b6820

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable {M₁ M₂ C₁ C₂ : Type} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂] {γ : Kˣ}
  {Φ₁ : M₁ →ₗ[R] K} {π₁ : M₁ →ₗ[R] C₁} {g₁ : M₁} {lam₁ : C₁ →ₗ[R] KR R}
  {Φ₂ : M₂ →ₗ[R] K} {π₂ : M₂ →ₗ[R] C₂} {g₂ : M₂} {lam₂ : C₂ →ₗ[R] KR R}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (Ψ : M₁ ≃ₗ[R] M₂) (hg : Ψ g₁ = g₂) : ∃ φ : C₁ ≃ₗ[R] C₂, ∀ x, φ (π₁ x) = π₂ (Ψ x) := by
  have hker1 : ∀ x, π₁ x = 0 → π₂ (Ψ x) = 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := D₁.ker x hx
    rw [map_smul, hg, map_smul, D₂.pg, smul_zero]
  have hker2 : ∀ y, π₂ y = 0 → π₁ (Ψ.symm y) = 0 := by
    intro y hy
    obtain ⟨r, rfl⟩ := D₂.ker y hy
    rw [map_smul, ← hg, LinearEquiv.symm_apply_apply, map_smul, D₁.pg, smul_zero]
  let e₁ := π₁.quotKerEquivOfSurjective D₁.surj
  let e₂ := π₂.quotKerEquivOfSurjective D₂.surj
  let f : (M₁ ⧸ LinearMap.ker π₁) →ₗ[R] (M₂ ⧸ LinearMap.ker π₂) :=
    (LinearMap.ker π₁).mapQ (LinearMap.ker π₂) Ψ.toLinearMap (fun x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
      exact hker1 x hx)
  let g : (M₂ ⧸ LinearMap.ker π₂) →ₗ[R] (M₁ ⧸ LinearMap.ker π₁) :=
    (LinearMap.ker π₂).mapQ (LinearMap.ker π₁) Ψ.symm.toLinearMap (fun y hy => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hy ⊢
      exact hker2 y hy)
  let F : (M₁ ⧸ LinearMap.ker π₁) ≃ₗ[R] (M₂ ⧸ LinearMap.ker π₂) :=
    LinearEquiv.ofLinear f g (by ext y; simp [f, g]) (by ext x; simp [f, g])
  refine ⟨(e₁.symm.trans F).trans e₂, fun x => ?_⟩
  have h1 : e₁.symm (π₁ x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e₁]
  simp only [LinearEquiv.trans_apply]
  rw [h1]
  simp [F, f, e₂]
end Formalism.FourierDecayAlt.P.A5x8
