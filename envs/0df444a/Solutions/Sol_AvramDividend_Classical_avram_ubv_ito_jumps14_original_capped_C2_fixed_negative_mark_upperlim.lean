-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:45:50.120374+00:00
-- url     : https://prove2.me/submissions/811214fd-f913-450f-9f22-d9155fb170fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_fixed_negative_mark_Taylor_correction_upperlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Real capped C² data imply the derivative continuity needed at a zero-contact jump. -/
theorem solution
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y z : ℝ) (hy : y ∈ Ioo (0 : ℝ) c) (hz : z < 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0) ≤
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0) + ε := by
  have hc2 : ContDiffOn ℝ 2 w (Ioo (0 : ℝ) c) :=
    avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
      cap c hc hcCap w hw_smooth
  have hderOn : ContinuousOn (deriv w) (Ioo (0 : ℝ) c) :=
    hc2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hder : ContinuousAt (deriv w) y :=
    hderOn.continuousAt (isOpen_Ioo.mem_nhds hy)
  have hwy : ContinuousAt w y := by
    apply hwcont.continuousAt
    apply mem_of_superset (Ioi_mem_nhds hy.1)
    exact Ioi_subset_Ici_self
  exact avram_ubv_ito_jumps14_fixed_negative_mark_Taylor_correction_upperlim
    w hw0 hwcont hwneg y z hy.1 hz hwy hder u hu
