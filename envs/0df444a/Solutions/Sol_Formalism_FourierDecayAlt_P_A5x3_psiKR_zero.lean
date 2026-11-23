-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.psiKR_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:41.166825+00:00
-- url     : https://prove2.me/submissions/49c42b95-cc2d-4d73-998e-4f8ab27576f4

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
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable {C : Type} [AddCommGroup C] [Module R C]
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) :
    psiKR R ψ (0 : KR R) = 1 := (psiBar h).map_zero_eq_one
end Formalism.FourierDecayAlt.P.A5x3
