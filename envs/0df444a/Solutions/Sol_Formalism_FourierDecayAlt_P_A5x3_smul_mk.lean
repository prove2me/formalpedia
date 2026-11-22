-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.smul_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:36.240139+00:00
-- url     : https://prove2.me/submissions/1bc98f66-2c5c-4417-a674-33d59a898b91

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
theorem _root_.solution (r : R) (x : K) :
    r • (Submodule.Quotient.mk x : KR R) = Submodule.Quotient.mk ((r : K) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl
end Formalism.FourierDecayAlt.P.A5x3
