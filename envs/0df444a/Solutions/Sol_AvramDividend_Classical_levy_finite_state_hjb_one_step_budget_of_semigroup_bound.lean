-- Prove2me | solution 1 for AvramDividend.Classical.levy_finite_state_hjb_one_step_budget_of_semigroup_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:17:27.847631+00:00
-- url     : https://prove2.me/submissions/7ccb3584-5129-4de0-9e1f-6b2e8cb1ffe8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve
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
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (u a : ι → ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (q : ℝ)
    (hI : ∀ i, Integrable
      (fun ω => w (u i - a i + X.X (t - s) ω)) P)
    (hsec : ∀ i, a i ≤ w (u i) - w (u i - a i))
    (hsemi : ∀ i,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ ω, w (u i - a i + X.X (t - s) ω) ∂P) ≤ w (u i - a i)) :
    ∀ᵐ ω ∂P,
      a (p ω) +
        Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u (p η) - a (p η) +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u (p ω)) := by
  have hm :=
    AvramDividend.Classical.levy_increment_condExp_finite_valued_reserve
      X s t hst p hp (fun i => u i - a i) w hw hI
  filter_upwards [hm] with ω hω
  rw [hω]
  have hstep := hsec (p ω)
  have htrans := hsemi (p ω)
  linarith
