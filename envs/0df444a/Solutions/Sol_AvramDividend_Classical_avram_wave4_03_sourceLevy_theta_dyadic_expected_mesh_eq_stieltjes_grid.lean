-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_dyadic_expected_mesh_eq_stieltjes_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:25:02.235227+00:00
-- url     : https://prove2.me/submissions/f1d5b44c-d9cd-4ea6-aa99-e08a06d88b27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every right upper-dyadic theta-exponential Stieltjes mesh has an exact
full random dividend-measure finite-cell representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (θ : ℝ)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (θ * Real.exp (θ *
          (X.X u ω - rightLimit D u ω) - (u : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) =
    (∫⁻ ω, ∫⁻ s : ℝ,
      ∑ i ∈ Finset.range (2 ^ n),
        if s ∈ Ioc (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
            ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ) then
          ENNReal.ofReal (θ * Real.exp (θ *
            (X.X ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω -
              rightLimit D ((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω) -
            (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) * X.ψ θ))
        else 0 ∂dividendMeasure D ω ∂P) := by
  classical
  apply lintegral_congr_ae
  filter_upwards [] with ω
  apply lintegral_congr_ae
  filter_upwards [] with s
  let a : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (θ * Real.exp (θ *
      (X.X (((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω -
        rightLimit D (((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω) -
      ((((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) * X.ψ θ))
  exact (avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling T hT s n a).symm
