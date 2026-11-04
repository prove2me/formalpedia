-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:01:40.997213+00:00
-- url     : https://prove2.me/submissions/fc56ce98-e500-49cc-b5a6-f4c5fc3bd9f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- Apply the genuine pathwise deterministic jump-sum limit to each
original Lévy sample path centred at its initial value, with no
expectation exchange or independent process construction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ)) :
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω - X.X 0 ω
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        f (Y u - Function.leftLim Y u) ≠ 0) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ F, f (Y u - Function.leftLim Y u))) := by
  obtain ⟨hR, hL⟩ :=
    avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag X ω
  exact avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits
    (fun v : ℝ≥0 => X.X v ω - X.X 0 ω)
    T hT f hf hneg hL hR
