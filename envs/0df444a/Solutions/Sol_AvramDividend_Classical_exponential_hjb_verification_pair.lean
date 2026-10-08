-- Prove2me | solution 1 for AvramDividend.Classical.exponential_hjb_verification_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:32:16.687863+00:00
-- url     : https://prove2.me/submissions/ba1096ab-1eb2-41a2-9034-a553a9a21476

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exponential_generator_discount_supersolution
import Theorems.Thm_AvramDividend_Classical_exponential_gradient_ge_one_of_ge_one_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q : ℝ) (hθ : 1 ≤ θ) (hψ : X.ψ θ ≤ q) :
    ∀ x : ℝ, 0 ≤ x →
      (X.generator (fun y : ℝ => Real.exp (θ * y)) x -
        q * Real.exp (θ * x) ≤ 0) ∧
      (1 ≤ deriv (fun y : ℝ => Real.exp (θ * y)) x) := by
  intro x hx
  exact ⟨exponential_generator_discount_supersolution X θ q x hψ,
    exponential_gradient_ge_one_of_ge_one_nonneg θ x hθ hx⟩
