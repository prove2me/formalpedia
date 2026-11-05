-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:51:04.897228+00:00
-- url     : https://prove2.me/submissions/e81d5726-cb55-494f-80ac-53a439b4f9fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (T a : ℝ) :
    Tendsto
      (fun m : ℕ =>
        ((m : ℝ) * ((m : ℝ) - 1) / 2) *
          ((T * a) ^ 2 / (m : ℝ) ^ 2))
      atTop (𝓝 ((T * a) ^ 2 / 2)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hnat
  have hshift :
      Tendsto (fun n : ℕ => (1 : ℝ) - (n : ℝ)⁻¹) atTop
        (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hinv)
  have hmain :
      Tendsto
        (fun n : ℕ => ((T * a) ^ 2 / 2) * (1 - (n : ℝ)⁻¹))
        atTop (𝓝 ((T * a) ^ 2 / 2)) := by
    simpa only [mul_one] using (tendsto_const_nhds.mul hshift)
  apply hmain.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  field_simp [hn0]
