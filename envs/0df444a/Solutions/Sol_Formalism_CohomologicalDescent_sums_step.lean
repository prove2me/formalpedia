-- Prove2me | solution 1 for Formalism.CohomologicalDescent.sums_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:10.892964+00:00
-- url     : https://prove2.me/submissions/9be4be7d-82f0-4f4a-b589-1b086114bacd

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution (c x0 : ℝ) (hc : 0 < c) (hx0 : 0 < x0) (d : ℕ) (hd : 1 ≤ d) :
    min (c / x0) (c / (d : ℝ)) ≤ sums_G c x0 d - sums_G c x0 ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd' : (d : ℝ) ≠ 0 := hdpos.ne'
  have hx0' : x0 ≠ 0 := hx0.ne'
  unfold sums_G
  by_cases h1 : (d : ℝ) ≤ x0
  · have h2 : (d : ℝ) - 1 ≤ x0 := by linarith
    rw [if_pos h1, if_pos h2]
    have e : c / x0 * d - c / x0 * (d - 1) = c / x0 := by ring
    rw [e]
    exact min_le_left _ _
  · rw [not_le] at h1
    by_cases h2 : (d : ℝ) - 1 ≤ x0
    · rw [if_neg (not_le.2 h1), if_pos h2]
      refine le_trans (min_le_right _ _) ?_
      have hlog : 1 - x0 / d ≤ Real.log (d / x0) := by
        have := Real.one_sub_inv_le_log_of_pos (div_pos hdpos hx0)
        rwa [inv_div] at this
      have hq : 0 ≤ (d - x0) * (x0 - (d - 1)) := mul_nonneg (by linarith) (by linarith)
      have e : c + c * (1 - x0 / d) - c / x0 * (d - 1) - c / d =
          c * ((d - x0) * (x0 - (d - 1))) / (x0 * d) := by
        field_simp
        ring
      have hnn : 0 ≤ c * ((d - x0) * (x0 - (d - 1))) / (x0 * d) :=
        div_nonneg (mul_nonneg hc.le hq) (mul_pos hx0 hdpos).le
      have hcl := mul_le_mul_of_nonneg_left hlog hc.le
      linarith
    · rw [not_le] at h2
      rw [if_neg (not_le.2 h1), if_neg (not_le.2 h2)]
      refine le_trans (min_le_right _ _) ?_
      have hdm : 0 < (d : ℝ) - 1 := by linarith
      have hdm' : (d : ℝ) - 1 ≠ 0 := hdm.ne'
      have hlog : Real.log (d / x0) - Real.log ((d - 1) / x0) = Real.log (d / (d - 1)) := by
        rw [Real.log_div hd' hx0', Real.log_div hdm' hx0', Real.log_div hd' hdm']
        ring
      have hlog' : c * Real.log (d / x0) - c * Real.log ((d - 1) / x0) = c * Real.log (d / (d - 1)) := by
        rw [← mul_sub, hlog]
      have hlb : 1 - (d - 1) / d ≤ Real.log (d / (d - 1)) := by
        have := Real.one_sub_inv_le_log_of_pos (div_pos hdpos hdm)
        rwa [inv_div] at this
      have e : c / d = c * (1 - (d - 1) / d) := by
        rw [one_sub_div hd']
        ring
      have hcl := mul_le_mul_of_nonneg_left hlb hc.le
      rw [e]
      linarith
end Formalism.CohomologicalDescent
