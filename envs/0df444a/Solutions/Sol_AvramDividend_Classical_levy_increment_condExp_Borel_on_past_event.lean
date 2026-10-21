-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_Borel_on_past_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:13:17.841527+00:00
-- url     : https://prove2.me/submissions/41c2068c-4cea-4369-90f0-e094de127b6f

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_payoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (x : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (hInt : Integrable (fun ω => f (x + X.X (t - s) ω)) P) :
    P[A.indicator (fun ω => f (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P) := by
  let F : Ω → ℝ := fun ω => f (x + (X.X t ω - X.X s ω))
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let h : ℝ → ℝ := fun y => f (x + y)
  have hh : Measurable h :=
    hf.comp (measurable_const.add measurable_id)
  have hid : IdentDistrib F
      (fun ω => f (x + X.X (t - s) ω)) P P := by
    simpa only [Function.comp_def, F, h, g] using
      (X.stationaryIncrements s t hst).comp hh
  have hFI : Integrable F P := hid.integrable_iff.mpr hInt
  have hIndicator :
      P[A.indicator F | 𝓕 s] =ᵐ[P]
        A.indicator (P[F | 𝓕 s]) :=
    condExp_indicator hFI hA
  have hMarkov :
      P[F | 𝓕 s] =ᵐ[P]
        (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P) :=
    levy_increment_condExp_Borel_payoff X s t hst x f hf hInt
  change P[A.indicator F | 𝓕 s] =ᵐ[P]
    A.indicator (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P)
  filter_upwards [hIndicator, hMarkov] with ω hI hM
  rw [hI]
  by_cases hw : ω ∈ A
  · simp [Set.indicator_of_mem hw, hM]
  · simp [Set.indicator, hw]
