-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_two_sided_killed_scale_markov_grid_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:11:51.011325+00:00
-- url     : https://prove2.me/submissions/baa688d9-a752-4323-bdca-7e343a8812ef

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_countable_two_sided_killed_scale_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_survival_schedule_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- The genuine continuously two-sided-killed q-scale reward is a Markov grid kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (a : ℝ) (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ H ω + (X.X (s + v) ω - X.X s ω) ∧
        H ω + (X.X (s + v) ω - X.X s ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if ∀ j : ℕ, τ j ≤ T →
        0 ≤ h + y (τ j) ∧ h + y (τ j) ≤ a
       then ENNReal.ofReal
         (Real.exp (-(q * (t : ℝ))) * W (h + y t))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
      ∂(Measure.map H P) := by
  calc
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ H ω + (X.X (s + v) ω - X.X s ω) ∧
        H ω + (X.X (s + v) ω - X.X s ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    (∫⁻ ω,
      if ∀ j : ℕ, τ j ≤ T →
        0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω) ∧
        H ω + (X.X (s + τ j) ω - X.X s ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) := by
        refine lintegral_congr ?_
        intro ω
        rw [chat04_random_reserve_shifted_two_sided_survival_schedule_iff
          X H ω a s T τ hCover hTerminal]
    _ = ∫⁻ h, ∫⁻ y,
      (if ∀ j : ℕ, τ j ≤ T →
        0 ≤ h + y (τ j) ∧ h + y (τ j) ≤ a
       then ENNReal.ofReal
         (Real.exp (-(q * (t : ℝ))) * W (h + y t))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
      ∂(Measure.map H P) :=
      chat04_countable_two_sided_killed_scale_markov_tonelli
        X s H hH τ T t a q W
        (chat04_scaleFunction_measurable_of_punctured_continuity X q W hW)
