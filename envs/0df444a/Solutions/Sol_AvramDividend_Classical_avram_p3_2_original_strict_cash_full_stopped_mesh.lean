-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_cash_full_stopped_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:32:34.981209+00:00
-- url     : https://prove2.me/submissions/030040de-63f4-4b4e-a503-c4a55a259069

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_discounted_mesh_sum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_mesh_terminal_clip
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_ennreal_truncated_clock_toNNReal_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original dividend cash strictly before T over the entire stopped
time interval is exactly the finite sum over its m+1 physical mesh cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let B : Set ℝ :=
      paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ)
    (∫⁻ t in B ∩ Ioc (0 : ℝ) (τ : ℝ),
      f t ∂(dividendMeasure D ω)) =
      ∑ i ∈ Finset.range (m + 1),
        (∫⁻ t in B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂(dividendMeasure D ω)) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let B : Set ℝ :=
    paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ)
  have hτ : τ ≤ T :=
    avram_p3_2_ennreal_truncated_clock_toNNReal_le
      (ruinTime X x D ω) T
  have hEnd : u (m + 1) = τ := by
    exact avram_p3_2_physical_mesh_terminal_clip T τ m hτ
  have hSum :=
    avram_p3_2_original_strict_cash_discounted_mesh_sum
      X x D ω T m (m + 1) f
  change (∫⁻ t in B ∩ Ioc (0 : ℝ) (u (m + 1) : ℝ),
    f t ∂(dividendMeasure D ω)) =
      ∑ i ∈ Finset.range (m + 1),
        (∫⁻ t in B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂(dividendMeasure D ω)) at hSum
  rw [hEnd] at hSum
  exact hSum
