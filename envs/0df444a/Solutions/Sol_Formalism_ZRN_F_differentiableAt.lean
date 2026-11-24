-- Prove2me | solution 1 for Formalism.ZRN.F_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:30.496623+00:00
-- url     : https://prove2.me/submissions/1065ece1-fa6d-455b-a657-aa32bae3fc07

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_e_differentiable
import Theorems.Thm_Formalism_ZRN_e_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (s₀ : ℂ) (h : 0 < s₀.re) : DifferentiableAt ℂ F s₀ := by
  obtain ⟨r, hr, u, hu, hb⟩ := e_dom s₀ h
  have hd : DifferentiableOn ℂ F (Metric.ball s₀ r) :=
    differentiableOn_tsum_of_summable_norm hu (fun n => (e_differentiable n).differentiableOn)
      Metric.isOpen_ball hb
  exact hd.differentiableAt (Metric.ball_mem_nhds s₀ hr)
end Formalism.ZRN
