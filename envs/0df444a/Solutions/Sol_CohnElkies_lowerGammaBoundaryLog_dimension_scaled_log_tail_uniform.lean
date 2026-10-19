-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/e92ef475-3f76-41e4-b8d6-7de91e10e530

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_antitoneOn
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      (by exact_mod_cast hd)
  have ht : 0 < Real.pi * |Y| / 2 := by positivity
  have ht' : 0 < Real.pi * |((d : ℝ) / 2) * Y| / 2 := by
    positivity
  have hcompare :
      Real.pi * |Y| / 2 ≤
        Real.pi * |((d : ℝ) / 2) * Y| / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ (d : ℝ) / 2)]
    nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg Y),
      mul_nonneg (sub_nonneg.mpr hℓ)
        (mul_nonneg Real.pi_pos.le (abs_nonneg Y))]
  have hcoth := lowerCoth_log_antitoneOn ht ht' hcompare
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail
    hdpos hc hY
  linarith
end CohnElkies
