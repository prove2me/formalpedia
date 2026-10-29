-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:54:18.057491+00:00
-- url     : https://prove2.me/submissions/f6fb6319-3795-48a7-b66d-5ae7b970fe04

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) =>
        (2 : ℝ) ^ n *
          ((((2 : ℝ≥0)⁻¹) ^ n : ℝ≥0) * X.drift -
            X.X ((2 : ℝ≥0)⁻¹ ^ n) ω))
      atTop (fun _ => (0 : ℝ)) := by
  haveI := X.isProbability
  let δ : ℕ → ℝ≥0 := fun n => ((2 : ℝ≥0)⁻¹) ^ n
  let θ : ℕ → ℝ := fun n => (2 : ℝ) ^ n
  have hθ : Tendsto θ atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hθge : ∀ n, 1 ≤ θ n := by
    intro n
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hProduct : ∀ n, (δ n : ℝ) * θ n = (1 : ℝ) := by
    intro n
    simp only [δ, θ, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
    rw [← mul_pow]
    norm_num
  let D : ℕ → Ω → ℝ :=
    fun n ω => θ n * ((δ n : ℝ) * X.drift - X.X (δ n) ω)
  have hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ D n ω := by
    intro n
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV (δ n)]
      with ω hw
    exact mul_nonneg (le_trans zero_le_one (hθge n)) (sub_nonneg.mpr hw)
  have hTail : ∀ a : ℝ, 0 < a →
      Tendsto (fun n => P.real {ω | a ≤ D n ω}) atTop (𝓝 0) := by
    intro a ha
    exact bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
      X hBV δ θ 1 hθ hθge hProduct a ha
  have hProb := bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
    P D hNonneg hTail
  simpa only [D, δ, θ] using hProb
