-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_unconditional_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:02:25.507775+00:00
-- url     : https://prove2.me/submissions/03e9e523-9fe0-4fc3-826a-8fe62cc74676

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_limit_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_of_measurable_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Genuine BV finite-horizon first-grid scale expectations converge without a separate measurable-limit premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    :
    Integrable (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω, (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) ω ∂P)) := by
  exact avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_of_measurable_limit
    X hX q hq W hW hBV θ hθ hψ a x ha hx0 hxa T mesh hmesh hpos K hK
    (avram_ws01b_bv_ceiling_grid_scale_limit_aestrongly_measurable
      X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK)
