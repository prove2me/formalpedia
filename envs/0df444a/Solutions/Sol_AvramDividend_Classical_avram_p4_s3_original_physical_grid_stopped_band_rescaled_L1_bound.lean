-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_physical_grid_stopped_band_rescaled_L1_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:14:58.588969+00:00
-- url     : https://prove2.me/submissions/9c454393-3a70-444f-8904-96a11c24a67f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true stopped negative-band count has uniformly bounded rescaled
    first moment over the physical grid T/k. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ k ω, τ k ω ≤ T / (k : ℝ≥0))
    (hKmeas : ∀ k, Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (k : ℕ) (hk : 0 < k) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    (k : ℝ) * (∫ ω, (K ω : ℝ) ∂P) ≤
      (T : ℝ) * (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let rate : ℝ := (T : ℝ) * (X.ν B).toReal
  change (k : ℝ) * (∫ ω, (K ω : ℝ) ∂P) ≤ rate
  have hM :=
    avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
      X (T / (k : ℝ≥0)) n (τ k) (hτ k) (hKmeas k)
  have hBound := hM.2
  change (∫ ω, (K ω : ℝ) ∂P) ≤
    ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) at hBound
  have hRate :
      ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) =
        rate / (k : ℝ) := by
    simpa [rate] using
      (avram_p4_f2_physical_horizon_rate_real_div T (X.ν B) k hk)
  rw [hRate] at hBound
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    (k : ℝ) * (∫ ω, (K ω : ℝ) ∂P)
        ≤ (k : ℝ) * (rate / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hBound (le_of_lt hkpos)
    _ = rate := by field_simp [ne_of_gt hkpos]
