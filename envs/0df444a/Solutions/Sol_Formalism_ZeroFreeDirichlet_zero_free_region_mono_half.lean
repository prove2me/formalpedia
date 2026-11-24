-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zero_free_region_mono_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:12.030676+00:00
-- url     : https://prove2.me/submissions/a81f8cde-c3eb-477f-a475-40b1ff90abf8

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_analytic_conductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {c₁ : ℝ} (hc : 0 < c₁) (q : ℕ) [NeZero q] (s : ℂ)
    (h : InRegion (c₁ / 2) q s) : InRegion c₁ q s := by
  unfold InRegion at h ⊢
  have hL : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_analytic_conductor q s.im)
  have h2 : c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le hL (by linarith)
  linarith
end Formalism.ZeroFreeDirichlet
