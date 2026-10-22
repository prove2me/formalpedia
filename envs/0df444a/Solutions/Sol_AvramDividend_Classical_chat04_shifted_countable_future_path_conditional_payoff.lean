-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_countable_future_path_conditional_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:30:59.441023+00:00
-- url     : https://prove2.me/submissions/ccedd0be-2fb2-4c08-8e8e-a53da91b9081

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_countable_path_independent_of_all_finite_prefixes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Conditional expectation of any integrable Borel functional of a countably
observed shifted Lévy future path is its unconditional expectation.
Finite-prefix joint independence is the exact assumption. This applies
to grid survival, first-exit events and discounted path-dependent payoffs.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hFinite : ∀ n : ℕ,
      Indep (⨆ i : Fin n, MeasurableSpace.comap
        (fun ω => X.X (s + τ i.val) ω - X.X s ω) inferInstance)
        (𝓕 s) P)
    (f : (ℕ → ℝ) → ℝ) (hf : Measurable f)
    (hInt : Integrable (fun ω => f (fun j => X.X (s + τ j) ω - X.X s ω)) P) :
    P[(fun ω => f (fun j => X.X (s + τ j) ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, f (fun j => X.X (s + τ j) ω - X.X s ω) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℕ → ℝ) :=
    fun ω j => X.X (s + τ j) ω - X.X s ω
  let F : Ω → ℝ := fun ω => f (Y ω)
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro j
    have hXt : Measurable (X.X (s + τ j)) :=
      (X.adapted (s + τ j)).mono (𝓕.le (s + τ j)) le_rfl
    have hXs : Measurable (X.X s) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact hXt.sub hXs
  have hFm : Measurable F := hf.comp hY
  have hStrong :
      StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hle :
      MeasurableSpace.comap F inferInstance ≤
        MeasurableSpace.comap Y inferInstance := by
    have h0 :
        (MeasurableSpace.comap f inferInstance).comap Y ≤
          (inferInstance : MeasurableSpace (ℕ → ℝ)).comap Y :=
      MeasurableSpace.comap_mono hf.comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      F] using h0
  have hPath :
      Indep (MeasurableSpace.comap Y inferInstance) (𝓕 s) P := by
    simpa only [Y] using
      (AvramDividend.Classical.chat04_shifted_countable_path_independent_of_all_finite_prefixes
        X s τ hFinite)
  have hi : Indep (MeasurableSpace.comap F inferInstance) (𝓕 s) P :=
    indep_of_indep_of_le_left hPath hle
  have hCE := condExp_indep_eq hFm.comap_le (𝓕.le s) hStrong hi
  change P[F | 𝓕 s] =ᵐ[P] (fun _ => ∫ ω, F ω ∂P)
  exact hCE
