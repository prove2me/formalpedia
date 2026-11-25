-- Prove2me | solution 1 for Formalism.CohomologicalDescent.harmonicMinSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:25:50.86073+00:00
-- url     : https://prove2.me/submissions/dbbab8ab-bdee-4131-a368-1b0e9fc454f6

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Theorems.Thm_Formalism_CohomologicalDescent_sums_step
import Theorems.Thm_Formalism_CohomologicalDescent_sums_tele

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
theorem _root_.solution : SharperSize := by
  intro k m h hm hmk hh
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hm hmk)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hk' : (k : ℝ) ≠ 0 := hk0.ne'
  have hc : 0 < (m : ℝ) * h := mul_pos hm0 hh0
  have hx0 : 0 < (m : ℝ) * h / k := div_pos hc hk0
  have hck : (m : ℝ) * h / ((m : ℝ) * h / k) = k := by
    rw [div_div_eq_mul_div, div_eq_iff hc.ne']
    ring
  have hterm : ∀ d ∈ Finset.Icc 1 h, min (k : ℝ) (((m : ℝ) * h) / d) ≤
      sums_G ((m : ℝ) * h) ((m : ℝ) * h / k) d -
        sums_G ((m : ℝ) * h) ((m : ℝ) * h / k) ((d : ℝ) - 1) := by
    intro d hd
    have := sums_step ((m : ℝ) * h) ((m : ℝ) * h / k) hc hx0 d
      (Finset.mem_Icc.1 hd).1
    rwa [hck] at this
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [sums_tele]
  have h0 : sums_G ((m : ℝ) * h) ((m : ℝ) * h / k) 0 = 0 := by
    unfold sums_G
    rw [if_pos hx0.le]
    ring
  rw [h0, sub_zero]
  unfold sums_G
  split_ifs with hle
  · rw [hck]
    have hkm : (k : ℝ) * h ≤ (m : ℝ) * h := by
      have h1 := mul_le_mul_of_nonneg_left hle hk0.le
      have e : (k : ℝ) * ((m : ℝ) * h / k) = (m : ℝ) * h := by
        field_simp
      linarith
    have hlog : 0 ≤ Real.log ((k : ℝ) / m) := Real.log_nonneg ((one_le_div hm0).2 hmk')
    nlinarith [mul_nonneg hc.le hlog]
  · have e : (h : ℝ) / ((m : ℝ) * h / k) = k / m := by
      rw [div_div_eq_mul_div, div_eq_div_iff hc.ne' hm0.ne']
      ring
    rw [e]
    exact le_of_eq (by ring)
end Formalism.CohomologicalDescent
