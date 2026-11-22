-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.rowFun_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:36.019666+00:00
-- url     : https://prove2.me/submissions/53b17106-a92a-451a-97fe-4df428acc7d5

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
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (a : Fin n) (v : Fin n → R) :
    rowFun R Z a v = Submodule.Quotient.mk ((Z⁻¹ *ᵥ coeLin R v) a) := rfl
end Formalism.FourierDecayAlt.P.A5x3
