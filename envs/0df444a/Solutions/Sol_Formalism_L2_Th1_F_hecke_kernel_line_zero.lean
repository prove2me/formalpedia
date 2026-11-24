-- Prove2me | solution 1 for Formalism.L2.Th1.F.hecke_kernel_line_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:58.155356+00:00
-- url     : https://prove2.me/submissions/ad5167ab-6c20-42a6-893c-fef3083b74d4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_hk_tendsto
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_hk_int_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : HkRowZero := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ)))
    (Real.summable_abs_int_rpow (by norm_num)) (fun m => Hk3.hk_tendsto (m : ℂ)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact fun m => Hk3.hk_int_bound (le_of_lt hs) m
end Formalism.L2.Th1.F
