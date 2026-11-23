-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.isUnit_det_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:59.324495+00:00
-- url     : https://prove2.me/submissions/61955992-de8a-4f28-ad08-60f4581051cc

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI


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
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) : IsUnit (pt s t).det := Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI s t)
end Formalism.FourierDecayAlt.P.A5x5
