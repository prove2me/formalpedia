-- Prove2me | solution 1 for AvramDividend.Classical.levy_finite_state_hjb_one_step_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:36:17.738344+00:00
-- url     : https://prove2.me/submissions/c54847bf-473f-4634-883c-0324f50ac34d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap
import Theorems.Thm_AvramDividend_Classical_levy_finite_state_hjb_one_step_budget_of_semigroup_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
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
    (q : ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (ha : ∀ i, 0 ≤ a i) (hua : ∀ i, a i ≤ u i)
    (huC : ∀ i, ENNReal.ofReal (u i) ≤ C)
    (hI : ∀ i, Integrable
      (fun ω => w (u i - a i + X.X (t - s) ω)) P)
    (hsemi : ∀ i,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ ω, w (u i - a i + X.X (t - s) ω) ∂P) ≤ w (u i - a i)) :
    ∀ᵐ ω ∂P,
      a (p ω) +
        Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u (p η) - a (p η) +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u (p ω)) := by
  have hsec : ∀ i, a i ≤ w (u i) - w (u i - a i) := by
    intro i
    exact AvramDividend.Classical.local_verification_hjb_controls_dividend_jump_le_cap
      X q w C hw_cont hw_smooth hw_hjb
      (u i) (a i) (ha i) (hua i) (huC i)
  exact AvramDividend.Classical.levy_finite_state_hjb_one_step_budget_of_semigroup_bound
    X s t hst p hp u a w hw q hI hsec hsemi
