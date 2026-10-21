-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_finite_valued_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:18:16.80336+00:00
-- url     : https://prove2.me/submissions/ed861fa3-1654-4455-8b8e-14857c7d0f6c

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_simple_state

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (x : ι → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hI : ∀ i, Integrable (fun ω => f (x i + X.X (t - s) ω)) P) :
    P[(fun ω => f (x (p ω) + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ ω', f (x (p ω) + X.X (t - s) ω') ∂P) := by
  classical
  let A : ι → Set Ω := fun i => {ω | p ω = i}
  let F : ι → Ω → ℝ := fun i ω =>
    f (x i + (X.X t ω - X.X s ω))
  let E : ι → ℝ := fun i =>
    ∫ ω, f (x i + X.X (t - s) ω) ∂P
  have hS :=
    levy_increment_condExp_finite_simple_state X s t hst
      (Finset.univ : Finset ι) x f hf A
      (by intro i _; exact hp i)
      (by intro i _; exact hI i)
  have hleft (ω : Ω) :
      (∑ i ∈ (Finset.univ : Finset ι), (A i).indicator (F i) ω) =
        f (x (p ω) + (X.X t ω - X.X s ω)) := by
    calc
      _ = ∑ i ∈ (Finset.univ : Finset ι),
          if i = p ω then f (x i + (X.X t ω - X.X s ω)) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = p ω
        · subst i
          simp [A, F, Set.indicator]
        · have hne : p ω ≠ i := Ne.symm hi
          simp [A, F, Set.indicator, hi, hne]
      _ = f (x (p ω) + (X.X t ω - X.X s ω)) := by simp
  have hright (ω : Ω) :
      (∑ i ∈ (Finset.univ : Finset ι),
        (A i).indicator (fun _ => E i) ω) =
        ∫ ω', f (x (p ω) + X.X (t - s) ω') ∂P := by
    calc
      _ = ∑ i ∈ (Finset.univ : Finset ι),
          if i = p ω then E i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = p ω
        · subst i
          simp [A, Set.indicator]
        · have hne : p ω ≠ i := Ne.symm hi
          simp [A, Set.indicator, hi, hne]
      _ = E (p ω) := by simp
      _ = ∫ ω', f (x (p ω) + X.X (t - s) ω') ∂P := rfl
  have hLeftEq :
      (fun ω => f (x (p ω) + (X.X t ω - X.X s ω))) =
        (fun ω => ∑ i ∈ (Finset.univ : Finset ι),
          (A i).indicator (F i) ω) :=
    funext (fun ω => (hleft ω).symm)
  have hRightEq :
      (fun ω => ∫ ω', f (x (p ω) + X.X (t - s) ω') ∂P) =
        (fun ω => ∑ i ∈ (Finset.univ : Finset ι),
          (A i).indicator (fun _ => E i) ω) :=
    funext (fun ω => (hright ω).symm)
  rw [hLeftEq, hRightEq]
  exact hS
