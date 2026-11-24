-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.integrable_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:12.934185+00:00
-- url     : https://prove2.me/submissions/4df9f310-a695-45f5-807b-b1dce0aaf8a7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero

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
theorem _root_.solution {a : ℝ} (ha : 1 / 2 < a) : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-a)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * a)
    (by simp; linarith)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring
end Formalism.L2.Th1.F.Hk3
