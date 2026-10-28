-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_killed_scale_markov_tonelli_explicit_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:34:57.813448+00:00
-- url     : https://prove2.me/submissions/7687a587-0869-48f2-bbf3-949691085436

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_markov_tonelli_grid_kernel
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- A concrete Cantor schedule represents the continuously killed q-scale
reward through an independent shifted-path Markov kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ τ : ℕ → ℝ≥0,
      (∫⁻ ω,
        if ∀ v : ℝ≥0, v ≤ T →
            0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
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
  exact ⟨τ,
    chat04_true_killed_scale_markov_tonelli_grid_kernel
      X s H hH τ T t hCover hTerminal q W hW⟩
