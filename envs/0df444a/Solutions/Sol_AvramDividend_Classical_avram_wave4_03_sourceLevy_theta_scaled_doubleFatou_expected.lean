-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_doubleFatou_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:16:29.647967+00:00
-- url     : https://prove2.me/submissions/a92e69b2-bea6-459e-8196-f6510a3b0e18

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Positive exponential tilts preserve genuine source full-Stieltjes
double-Fatou convergence, including diffuse and singular dividend mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (θ * Real.exp (θ *
          (X.X u ω - rightLimit D u ω) - (u : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) atTop := by
  classical
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  have hmul : θ * (Real.log θ / θ) = Real.log θ := by
    field_simp
  have hid (u : ℝ≥0) (ω : Ω) :
      Real.exp (θ * (Real.log θ / θ + X.X u ω -
        rightLimit D u ω) - (u : ℝ) * X.ψ θ) =
      θ * Real.exp (θ * (X.X u ω - rightLimit D u ω) -
        (u : ℝ) * X.ψ θ) := by
    calc
      _ = Real.exp (Real.log θ +
        (θ * (X.X u ω - rightLimit D u ω) -
          (u : ℝ) * X.ψ θ)) := by
        congr 1
        rw [mul_sub, mul_add, hmul]
        ring
      _ = _ := by rw [Real.exp_add, Real.exp_log hθ]
  have hf := avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
    X (Real.log θ / θ) D hD θ (X.ψ θ) T hT
  simpa only [hid] using hf
