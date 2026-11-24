-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_pos_of_inRegion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:10.744804+00:00
-- url     : https://prove2.me/submissions/00aaf791-faa4-44a6-8c8b-ab07aa2e329c

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_mul_abs_add_two
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_mul_abs_add_two_pos

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
theorem _root_.solution {c : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hc : c ≤ 1 / 2) (hs : InRegion c q s) :
    0 < s.re := by
  unfold InRegion at hs
  have hL := log_two_le_log_mul_abs_add_two q s.im
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := div_le_div_of_nonneg_right hc hLpos.le
  have h2 : (1 / 2 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2pos hL
  have h3 : (1 / 2 : ℝ) / Real.log 2 < 1 := by
    rw [div_lt_one h2pos]; linarith [Real.log_two_gt_d9]
  linarith
end Formalism.ZeroFreeDirichlet
