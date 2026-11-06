-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_strategywise_cap_budget_to_both_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:50:03.359185+00:00
-- url     : https://prove2.me/submissions/147eaf05-1e07-47ce-b2f9-72c66945020c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Extract both variational bounds from every original admissible strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hStrategy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        dividendValue X q x D ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxC
    unfold valueFunctionLe
    refine iSup_le ?_
    intro D
    refine iSup_le ?_
    intro hD
    exact hStrategy x hx hxC D hD
  refine ⟨hCap, ?_⟩
  intro hTop x hx
  subst C
  simpa only [valueFunctionLe_top_eq_valueFunction] using hCap x hx (le_top)
