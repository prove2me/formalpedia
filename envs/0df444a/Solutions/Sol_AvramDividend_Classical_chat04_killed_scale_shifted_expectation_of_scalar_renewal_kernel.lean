-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:18:57.986008+00:00
-- url     : https://prove2.me/submissions/83d5a901-b2ad-4f23-9c18-54b453e14ff6

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_markov_tonelli_grid_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- Scalar killed-scale renewal gives the shifted random-reserve identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hScalar : ∀ h : ℝ,
      (∫⁻ y,
        (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
         then ENNReal.ofReal
           (Real.exp (-(q * (T : ℝ))) * W (h + y T))
         else (0 : ℝ≥0∞))
        ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)) =
      ENNReal.ofReal (W h)) :
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
      then ENNReal.ofReal
        (Real.exp (-(q * (T : ℝ))) *
          W (H ω + (X.X (s + T) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ENNReal.ofReal (W h) ∂(Measure.map H P) := by
  rw [chat04_true_killed_scale_markov_tonelli_grid_kernel
    X s H hH τ T T hCover hTerminal q W hW]
  refine lintegral_congr ?_
  intro h
  exact hScalar h
