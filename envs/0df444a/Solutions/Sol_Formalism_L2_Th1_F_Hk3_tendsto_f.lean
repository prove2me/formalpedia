-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.tendsto_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:55.524716+00:00
-- url     : https://prove2.me/submissions/c7008e8b-cd1d-4c11-b3ad-a14270bf9ac7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_bound_f

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
open Formalism.L2.Th1.F.Hk3
namespace Formalism.L2.Th1.F.Hk3
theorem _root_.solution {a : ℝ} (ha : 1 / 2 < a) {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => 1 + t ^ 2) l atTop) :
    Tendsto (fun t : ℝ => t * (1 + t ^ 2) ^ (-a)) l (𝓝 0) := by
  refine squeeze_zero_norm (fun t => bound_f t) ?_
  exact (tendsto_rpow_neg_atTop (y := a - 1 / 2) (by linarith)).comp hl
end Formalism.L2.Th1.F.Hk3
