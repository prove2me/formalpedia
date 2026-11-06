-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_void_rate_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:17:21.469194+00:00
-- url     : https://prove2.me/submissions/ab4de9ad-bcca-4146-b164-70f238406c61

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_nonvoid_second_order_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_bonferroni_void_rate_squeeze_atTop
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual negative-band jump occurrence has the physical Lévy intensity at small times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * P.real {ω : Ω |
        {u : ℝ≥0 | 0 < u ∧ u ≤ (k : ℝ≥0)⁻¹ ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard ≠ 0})
      Filter.atTop
      (nhds ((X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let rate : ℝ := (X.ν B).toReal
  let p : ℕ → ℝ := fun k =>
    P.real {ω : Ω |
      {u : ℝ≥0 | 0 < u ∧ u ≤ (k : ℝ≥0)⁻¹ ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard ≠ 0}
  change Tendsto (fun k : ℕ => (k : ℝ) * p k) atTop (nhds rate)
  have hScale (k : ℕ) (hk : 0 < k) :
      (((((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) =
        rate * (k : ℝ)⁻¹ := by
    simpa [div_eq_mul_inv, rate] using
      (avram_p4_f2_physical_horizon_rate_real_div
        (1 : ℝ≥0) (X.ν B) k hk)
  apply avram_p4_f2_bonferroni_void_rate_squeeze_atTop rate p
  intro k hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  let rk : ℝ := (((((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
  have h := avram_p4_f2_original_negative_band_nonvoid_second_order_bound
    X ((k : ℝ≥0)⁻¹) n
  change rk - rk ^ 2 / 2 ≤ p k ∧ p k ≤ rk at h
  have hr : rk = rate * (k : ℝ)⁻¹ := hScale k hk
  rw [hr] at h
  have hLower :
      rate - (rate ^ 2 / 2) * (k : ℝ)⁻¹ =
        (k : ℝ) * (rate * (k : ℝ)⁻¹ -
          (rate * (k : ℝ)⁻¹) ^ 2 / 2) := by
    field_simp [hk0] <;> ring
  have hUpper :
      (k : ℝ) * (rate * (k : ℝ)⁻¹) = rate := by
    field_simp [hk0] <;> ring
  constructor
  · calc
      rate - (rate ^ 2 / 2) * (k : ℝ)⁻¹ =
          (k : ℝ) * (rate * (k : ℝ)⁻¹ -
            (rate * (k : ℝ)⁻¹) ^ 2 / 2) := hLower
      _ ≤ (k : ℝ) * p k :=
        mul_le_mul_of_nonneg_left h.1 (le_of_lt hkpos)
  · calc
      (k : ℝ) * p k ≤
          (k : ℝ) * (rate * (k : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left h.2 (le_of_lt hkpos)
      _ = rate := hUpper
