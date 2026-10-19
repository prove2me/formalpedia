-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/05e84d7b-ddde-4ac9-b167-fd01d01fdb1e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
import Theorems.Thm_CohnElkies_lowerCoth_log_half_le_of_one_le_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : 1 ≤ |Y|) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
        ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * Real.exp 1 * c ^ 2 / |Y|) := by
  have hyzero : Y ≠ 0 := by
    intro hzero
    norm_num [hzero] at hY
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hyzero
  have hcorr := lowerCoth_log_half_le_of_one_le_abs hY
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast hd
  have hlog :
      Real.log (4 * Real.pi * Real.exp 1 * c ^ 2 / |Y|) =
        Real.log (4 * Real.pi * c ^ 2 / |Y|) + 1 := by
    have hfactor :
        4 * Real.pi * Real.exp 1 * c ^ 2 / |Y| =
          (4 * Real.pi * c ^ 2 / |Y|) * Real.exp 1 := by
      field_simp [abs_ne_zero.mpr hyzero]
    rw [hfactor,
      Real.log_mul
        (show 4 * Real.pi * c ^ 2 / |Y| ≠ 0 by positivity)
        (Real.exp_ne_zero _), Real.log_exp]
  rw [hlog]
  nlinarith
end CohnElkies
