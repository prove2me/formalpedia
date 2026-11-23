-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.added_block_kernel_block_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:25.561425+00:00
-- url     : https://prove2.me/submissions/e5144dbb-5f25-4a96-a6f7-b542bd8ab02f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_kernel_nonzero_modulus_determinant_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_added_block_kernel_modulus_det_eq

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
theorem _root_.solution : Formalism.FourierDecayAlt.A5.NsBlockDiag := by
  intro K _ _ _ R ψ hd h h' _
  exact ⟨fun h0 => kernel_nonzero_modulus_determinant_eq hd h h' h0, fun s t hne => added_block_kernel_modulus_det_eq hd h h' s t hne⟩
end Formalism.FourierDecayAlt.P
