-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_finite_killed_markov_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:33:43.184291+00:00
-- url     : https://prove2.me/submissions/51a09836-b9d2-4acd-9a47-5839acc16fb5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_esscher_survival_finite_markov_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_positive_kernel_map
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Exact source-Lévy killed Markov identity at finite deterministic horizons,
with the original-P future survival mass at the random current reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => ENNReal.ofReal (Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    (∫⁻ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp
          (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (∫ ζ,
          ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
            (fun ζ => Real.exp
              (θ * X.X u ζ - (u : ℝ) *
                laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)
       else (0 : ℝ≥0∞)) ∂P) := by
  classical
  let F : ℝ → ℝ := fun z =>
    ∫ ζ, ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ζ}).indicator
      (fun ζ => Real.exp
        (θ * X.X u ζ - (u : ℝ) *
          laplaceExponent X.c X.σ X.ν θ)) ζ ∂P
  have hF : Monotone F := by
    intro a b hab
    exact esscher_weighted_lower_survival_mass_monotone_start
      X θ hθ a b hab u
  calc
    _ = (∫⁻ h : ℝ × Bool,
      (if h.2 then
        ENNReal.ofReal (Real.exp
          (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (F (x + h.1))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P)) := by
        simpa only [F] using
          (avram_root29_01_esscher_survival_finite_markov_ennreal
            X θ hθ x s u τ hCover hTerminal)
    _ = _ := by
      simpa only [F] using
        (avram_root29_01_history_survival_positive_kernel_map
          X θ x s τ hCover F hF)
