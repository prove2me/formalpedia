-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_zero_clock_negative_band_marked_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:39:50.849603+00:00
-- url     : https://prove2.me/submissions/625ad5e3-c96d-44c4-888b-991bceeffcf6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original negative-band marked-time sum has no time-zero contribution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (τ : Ω → ℝ≥0) (ω : Ω) (hτ0 : τ ω = 0)
    (f : Ω → ℝ≥0 → ℝ) :
    ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
      X ω (τ ω) n).toFinset, f ω u = 0 := by
  classical
  let s : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  have hs : s.Finite :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n
  have hempty : s = ∅ := by
    ext u
    constructor
    · intro hu
      have ht : 0 < u := hu.1
      have hu0 : u ≤ 0 := by simpa only [hτ0] using hu.2.1
      exact False.elim ((not_lt_of_ge hu0) ht)
    · intro hu
      cases hu
  have hF : hs.toFinset = ∅ := by
    exact Set.Finite.toFinset_eq_empty.mpr hempty
  simp only [hF, Finset.sum_empty]
