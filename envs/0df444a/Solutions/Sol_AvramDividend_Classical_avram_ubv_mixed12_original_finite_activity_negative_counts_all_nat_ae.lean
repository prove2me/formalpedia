-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_counts_all_nat_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T16:36:30.039611+00:00
-- url     : https://prove2.me/submissions/16e323da-fb4d-4d22-92c1-fbebb9149d2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_count_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original negative jump marks are locally finite on one simultaneous
full-measure event, without excluding the Gaussian UBV regime. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) < ⊤ := by
  exact eventually_countable_forall.mpr (fun n : ℕ =>
    avram_ubv_mixed12_original_finite_activity_negative_count_ae
      X 0 (n : ℝ≥0) zero_le hFinite)
