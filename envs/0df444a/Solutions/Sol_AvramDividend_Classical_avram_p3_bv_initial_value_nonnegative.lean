-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_initial_value_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:50:19.504115+00:00
-- url     : https://prove2.me/submissions/aef54438-7c43-47cb-8570-e2f6405e6b53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original canonical nonnegative initial reserve and cap bound
force the verification candidate to be nonnegative at inception. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) :
    0 ≤ w x := by
  have hV := avram_p3_bv_allcap_linear_nonnegative
    C hC w hw_cont hw0 hw_smooth hw_grad x hx
  by_cases htop : C = ⊤
  · simpa [htop] using hV
  · have hxCap : x ≤ C.toReal := by
      have hle := ENNReal.toReal_mono htop hxc
      simpa [ENNReal.toReal_ofReal hx] using hle
    simpa [htop, hxCap] using hV
