-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.modulus_positive_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:52.229899+00:00
-- url     : https://prove2.me/submissions/d23fe1ee-1064-4c97-91c6-460bf65634b7

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_mul

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.ModMul := by
  intro K _ _ _ R ψ hd x y
  exact ⟨modK_pos hd.isOpen hd.isCompact x, modK_mul hd.isOpen hd.isCompact x y⟩
end Formalism.FourierDecayAlt.P
