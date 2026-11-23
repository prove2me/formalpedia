-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_liftE_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.561574+00:00
-- url     : https://prove2.me/submissions/188084c9-7b5d-44d6-85a7-13f7aa807c1a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂)
    (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ ≃ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) :
    π₂ (iso_liftE D₂ D₁ φ hφ x) = φ (π₁ x) ∧ Φ₂ (iso_liftE D₂ D₁ φ hφ x) = Φ₁ x := by
  exact iso_lift_spec D₂ D₁ (φ : C₁ →ₗ[R] C₂) hφ x
end Formalism.FourierDecayAlt.P.A5x8
