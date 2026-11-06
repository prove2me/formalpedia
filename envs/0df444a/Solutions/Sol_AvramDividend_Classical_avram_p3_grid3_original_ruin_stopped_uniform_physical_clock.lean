-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:23:45.677831+00:00
-- url     : https://prove2.me/submissions/6878cdf6-f20a-4fb2-a230-4a3b635703dc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u 0 = 0 ∧ u (m + 1) = min T τ ∧ Monotone u := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let v : ℕ → ℝ≥0 := fun i =>
    ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
  have hv : v 0 = 0 ∧ v (m + 1) = T ∧ Monotone v :=
    avram_p3_grid3_uniform_physical_clock_endpoints_monotone T m
  rcases hv with ⟨hv0, hvT, hvm⟩
  change min (v 0) τ = 0 ∧
    min (v (m + 1)) τ = min T τ ∧
    Monotone (fun i => min (v i) τ)
  refine ⟨?_, ?_, ?_⟩
  · have hz : (0 : ℝ≥0) ≤ τ := by positivity
    simpa only [hv0] using (min_eq_left hz)
  · simpa only [hvT]
  · intro i j hij
    exact min_le_min_right τ (hvm hij)
