-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.type_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:38.143448+00:00
-- url     : https://prove2.me/submissions/d1252a5b-13c7-4050-a5f1-2a14a78130df

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : TypeCS := by
  intro D Ty _ _ w amp hw
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [← Finset.mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hw d)
  calc ‖∑ t, amp t d‖ ^ 2 ≤ (∑ t, ‖amp t d‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset Ty)) (f := fun t => ‖amp t d‖)
      simpa using this
end Formalism.HermitianLatticeCounting.P.S4aux
