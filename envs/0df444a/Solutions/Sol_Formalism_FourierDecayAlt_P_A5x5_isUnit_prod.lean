-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.isUnit_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:57.676891+00:00
-- url     : https://prove2.me/submissions/38a0de18-b98c-460f-92a0-9b7dddddc237

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {n : ℕ} (f : Fin n → Kˣ) : IsUnit (∏ a : Fin n, ((f a : Kˣ) : K)) := by
  rw [← Units.coe_prod]
  exact Units.isUnit _
end Formalism.FourierDecayAlt.P.A5x5
