-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_ennreal_expectation_rightContinuous_of_uniform_l2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:39:42.173278+00:00
-- url     : https://prove2.me/submissions/40e5ea45-8cc8-4331-8646-42b59146b48d

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_expectation_rightContinuous_of_uniform_l2
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t₀ : ℝ≥0) :
    ContinuousWithinAt
      (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
      (Ici t₀) t₀ := by
  have h := chat04_killed_scale_expectation_rightContinuous_of_uniform_l2 X q hq W hW hzero θ x hθ hψ t₀
  have e : (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
      fun t : ℝ≥0 => ENNReal.ofReal (∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω ∂P) := by
    funext t
    exact chat04_history_killed_scale_real_ennreal_integral_bridge X q hq W hW θ x hθ hψ t
  rw [e]
  exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt h
