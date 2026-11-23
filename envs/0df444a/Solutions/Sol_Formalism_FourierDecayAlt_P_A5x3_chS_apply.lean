-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.chS_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:24.12486+00:00
-- url     : https://prove2.me/submissions/14f0ef02-c079-4578-8456-eec3e29918ae

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
variable {C : Type} [AddCommGroup C] [Module R C]
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (S : Submodule R (C →ₗ[R] KR R)) (c : C) (α : S) :
    chS h S c α = psiKR R ψ ((α : C →ₗ[R] KR R) c) := rfl
end Formalism.FourierDecayAlt.P.A5x3
