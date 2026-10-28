-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_killed_scale_unmasked_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:57:48.154462+00:00
-- url     : https://prove2.me/submissions/1f0d6601-c2d8-4778-a7f4-6ce68ef649c0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! A positive reserve makes history-killing inactive near time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hx : 0 < x) (W : ℝ → ℝ) (ω : Ω) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε →
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω =
          ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by
  obtain ⟨ε, hε, hsafe⟩ :=
    chat04_initial_safe_window_of_rightCont_zero X x hx ω (X.X_zero ω)
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hmem : ω ∈
      {u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u} := by
    intro s hs
    have hslt : s < ε := lt_of_le_of_lt hs ht
    have hlow := hsafe s hslt
    linarith
  rw [Set.indicator_of_mem hmem]
