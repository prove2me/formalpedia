-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.hk_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:21.176844+00:00
-- url     : https://prove2.me/submissions/42ce6441-5703-464a-95e2-51dbf8db2376

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul


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
theorem _root_.solution (w : ℂ) : Tendsto (fun s : ℝ => hk s w) (𝓝[>] 0) (𝓝 (1 / w ^ 2)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hk]
  · have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hc : Continuous (fun s : ℝ => hk s w) := by
      unfold hk
      refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
      exact Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [hk] using this
end Formalism.L2.Th1.F.Hk3
