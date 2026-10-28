-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_markov_tonelli_with_explicit_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:09:33.9939+00:00
-- url     : https://prove2.me/submissions/7839d935-8956-46f6-86e8-b498a29acbec

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_markov_tonelli_of_scaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- A concrete rational-and-terminal observation grid yields an exact
conditional Markov–Tonelli identity for every genuine q-scale function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ τ : ℕ → ℝ≥0,
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ∧
      (∃ j : ℕ, τ j = T) ∧
      (∫⁻ ω,
        if ∀ j : ℕ, τ j ≤ T →
          0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω)
        then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) *
            W (H ω + (X.X (s + t) ω - X.X s ω)))
        else (0 : ℝ≥0∞) ∂P) =
      ∫⁻ h, ∫⁻ y,
        (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
          then ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (h + y t))
          else (0 : ℝ≥0∞))
        ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
        ∂(Measure.map H P) := by
  obtain ⟨τ, hCover, hTerminal⟩ :=
    chat04_explicit_shifted_killed_survival_schedule T
  exact ⟨τ, hCover, hTerminal,
    chat04_killed_scale_markov_tonelli_of_scaleFunction
      X s H hH τ T t q W hW⟩
