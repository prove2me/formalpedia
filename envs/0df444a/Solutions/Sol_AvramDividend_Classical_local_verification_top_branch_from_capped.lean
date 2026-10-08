-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_top_branch_from_capped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:37:46.070677+00:00
-- url     : https://prove2.me/submissions/972aa4da-f650-429f-9fef-9489410c2bab

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (h : ∀ x : ℝ, 0 ≤ x →
       valueFunctionLe X q (⊤ : ℝ≥0∞) x ≤ ENNReal.ofReal (w x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x) := by
  intro x hx
  rw [← valueFunctionLe_top_eq_valueFunction (X := X) q x]
  exact h x hx
