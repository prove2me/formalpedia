-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.mk_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:56.154104+00:00
-- url     : https://prove2.me/submissions/8b1b372d-fa6a-4129-a8be-4490d9405169

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
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (x : K) : (Submodule.Quotient.mk x : KR R) = 0 ↔ x ∈ R := by
  rw [Submodule.Quotient.mk_eq_zero, mem_rng]
end Formalism.FourierDecayAlt.P.A5x3
