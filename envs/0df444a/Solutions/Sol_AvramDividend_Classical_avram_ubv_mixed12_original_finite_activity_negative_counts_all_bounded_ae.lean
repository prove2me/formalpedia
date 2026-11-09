-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T16:46:55.380648+00:00
-- url     : https://prove2.me/submissions/664844d2-a9cf-4214-80a1-8acad090c5b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_count_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked negative jump measure is locally finite on one
simultaneous full-measure set of every bounded horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ)) < ⊤ := by
  have hNat : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) < ⊤ := by
    exact eventually_countable_forall.mpr (fun n : ℕ =>
      avram_ubv_mixed12_original_finite_activity_negative_count_ae
        X 0 (n : ℝ≥0) zero_le hFinite)
  filter_upwards [hNat] with ω hω
  intro t
  let n : ℕ := Nat.ceil (t : ℝ)
  have hleReal : (t : ℝ) ≤ (n : ℝ) := Nat.le_ceil (t : ℝ)
  have htn : t ≤ (n : ℝ≥0) := by
    exact_mod_cast hleReal
  have hsub : Ioc (0 : ℝ≥0) t ×ˢ Iio (0 : ℝ) ⊆
      Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans htn⟩, hp.2⟩
  exact lt_of_le_of_lt (measure_mono hsub) (hω n)
