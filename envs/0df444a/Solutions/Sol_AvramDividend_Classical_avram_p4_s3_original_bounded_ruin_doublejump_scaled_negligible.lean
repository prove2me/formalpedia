-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_ruin_doublejump_scaled_negligible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:43:41.309247+00:00
-- url     : https://prove2.me/submissions/7d2f04c4-4674-4a8d-8567-4c200ca9cabe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_doublejump_probability_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- True stopped negative-band collision events are second-order at physical scale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : ℕ → Ω → ℝ≥0) (hτ : ∀ k ω, τ k ω ≤ T / (k : ℝ≥0)) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * P.real {ω : Ω |
        2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard})
      Filter.atTop (nhds (0 : ℝ)) := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let rate : ℝ := (T : ℝ) * (X.ν B).toReal
  let E : ℕ → ℝ := fun k =>
    P.real {ω : Ω |
      2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard}
  change Tendsto (fun k : ℕ => (k : ℝ) * E k) atTop (nhds (0 : ℝ))
  have hInv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hUpper : Tendsto (fun k : ℕ => (rate ^ 2 / 2) * (k : ℝ)⁻¹)
      atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hInv :
      Tendsto (fun k : ℕ => (rate ^ 2 / 2) * (k : ℝ)⁻¹)
        atTop (nhds ((rate ^ 2 / 2) * (0 : ℝ))))
  have hBounds :
      ∀ᶠ k : ℕ in atTop, (0 : ℝ) ≤ (k : ℝ) * E k ∧
        (k : ℝ) * E k ≤ (rate ^ 2 / 2) * (k : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have hc :=
      avram_p4_s3_original_bounded_stop_negative_band_doublejump_probability_bound
        X (T / (k : ℝ≥0)) n (τ k) (hτ k)
    change E k ≤
      (((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2) / 2 at hc
    have hr :
        ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) =
          rate / (k : ℝ) := by
      simpa [rate] using
        (avram_p4_f2_physical_horizon_rate_real_div T (X.ν B) k hk)
    rw [hr] at hc
    constructor
    · exact mul_nonneg (le_of_lt hkpos) ENNReal.toReal_nonneg
    · calc
        (k : ℝ) * E k ≤ (k : ℝ) * ((rate / (k : ℝ)) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hc (le_of_lt hkpos)
        _ = (rate ^ 2 / 2) * (k : ℝ)⁻¹ := by
          field_simp [hk0] <;> ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper
    (hBounds.mono (fun _ hk => hk.1))
    (hBounds.mono (fun _ hk => hk.2))
