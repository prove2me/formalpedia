-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.maximal_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:35.435949+00:00
-- url     : https://prove2.me/submissions/7056de47-35b3-497f-95a9-5450639695bc

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : MaxSum := by
  intro D _ w μ amp ε Mx hw hμ hε ha hM
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have h1 : ‖amp d‖ ^ 2 ≤ (ε * μ d) ^ 2 := by gcongr; exact ha d
  have h2 : (ε * μ d) ^ 2 ≤ ε ^ 2 * Mx * μ d := by
    have : μ d * μ d ≤ Mx * μ d := mul_le_mul_of_nonneg_right (hM d) (hμ d)
    nlinarith [sq_nonneg ε]
  calc w d * ‖amp d‖ ^ 2 ≤ w d * (ε ^ 2 * Mx * μ d) := mul_le_mul_of_nonneg_left (h1.trans h2) (hw d)
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P.S4aux
