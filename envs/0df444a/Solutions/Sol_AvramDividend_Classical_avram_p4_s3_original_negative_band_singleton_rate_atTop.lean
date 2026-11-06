-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_singleton_rate_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:47:10.367804+00:00
-- url     : https://prove2.me/submissions/5f56682d-a088-4630-ba01-ef211171364b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_singleton_second_order_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original one-negative-jump probability has its intrinsic Levy rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * P.real {ω : Ω |
        {u : ℝ≥0 | 0 < u ∧ u ≤ (k : ℝ≥0)⁻¹ ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard = 1})
      Filter.atTop
      (nhds ((X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let rate : ℝ := (X.ν B).toReal
  let p : ℕ → ℝ := fun k =>
    P.real {ω : Ω |
      {u : ℝ≥0 | 0 < u ∧ u ≤ (k : ℝ≥0)⁻¹ ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard = 1}
  change Tendsto (fun k : ℕ => (k : ℝ) * p k) atTop (nhds rate)
  have hScale (k : ℕ) (hk : 0 < k) :
      (((((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) =
        rate * (k : ℝ)⁻¹ := by
    simpa [div_eq_mul_inv, rate] using
      (avram_p4_f2_physical_horizon_rate_real_div
        (1 : ℝ≥0) (X.ν B) k hk)
  have hNat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      atTop (nhds (0 : ℝ)) := tendsto_inv_atTop_zero.comp hNat
  have hProd := (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => rate ^ 2) atTop (nhds (rate ^ 2))).mul hInv
  have hLower : Tendsto
      (fun k : ℕ => rate - rate ^ 2 * (k : ℝ)⁻¹)
      atTop (nhds rate) := by
    have hSub := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => rate) atTop (nhds rate)).sub hProd
    simpa using hSub
  have hBounds : ∀ᶠ k : ℕ in atTop,
      rate - rate ^ 2 * (k : ℝ)⁻¹ ≤ (k : ℝ) * p k ∧
      (k : ℝ) * p k ≤ rate := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    let rk : ℝ := (((((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    have h := avram_p4_s3_original_negative_band_singleton_second_order_bound
      X ((k : ℝ≥0)⁻¹) n
    change rk - rk ^ 2 ≤ p k ∧ p k ≤ rk at h
    have hr : rk = rate * (k : ℝ)⁻¹ := hScale k hk
    rw [hr] at h
    constructor
    · calc
        rate - rate ^ 2 * (k : ℝ)⁻¹ =
            (k : ℝ) * (rate * (k : ℝ)⁻¹ -
              (rate * (k : ℝ)⁻¹) ^ 2) := by
                field_simp [hk0] <;> ring
        _ ≤ (k : ℝ) * p k :=
          mul_le_mul_of_nonneg_left h.1 (le_of_lt hkpos)
    · calc
        (k : ℝ) * p k ≤
            (k : ℝ) * (rate * (k : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left h.2 (le_of_lt hkpos)
        _ = rate := by field_simp [hk0] <;> ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLower tendsto_const_nhds
    (hBounds.mono (fun _ hk => hk.1))
    (hBounds.mono (fun _ hk => hk.2))
