-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_killed_scale_markov_tonelli_grid_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:26:48.536121+00:00
-- url     : https://prove2.me/submissions/9f3673f4-aeb2-4f37-b7a6-68bec2a95b03

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_markov_tonelli_of_scaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- Genuine continuous-time killed q-scale reward has the Markov grid kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
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
  have hEvent : ∀ ω : Ω,
      (∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)) ↔
      (∀ j : ℕ, τ j ≤ T →
          0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω)) := by
    intro ω
    exact chat04_random_reserve_shifted_closed_survival_schedule_iff
      X H ω s T τ hCover hTerminal
  calc
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
      then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) *
            W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    (∫⁻ ω,
      if ∀ j : ℕ, τ j ≤ T →
          0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω)
      then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) *
            W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) := by
        refine lintegral_congr ?_
        intro ω
        by_cases hc : ∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
        · have hg := (hEvent ω).mp hc
          simp only [if_pos hc, if_pos hg]
        · have hg : ¬ (∀ j : ℕ, τ j ≤ T →
          0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω)) :=
            fun h => hc ((hEvent ω).mpr h)
          simp only [if_neg hc, if_neg hg]
    _ = ∫⁻ h, ∫⁻ y,
      (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
        then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (h + y t))
        else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
      ∂(Measure.map H P) :=
      chat04_killed_scale_markov_tonelli_of_scaleFunction
        X s H hH τ T t q W hW
