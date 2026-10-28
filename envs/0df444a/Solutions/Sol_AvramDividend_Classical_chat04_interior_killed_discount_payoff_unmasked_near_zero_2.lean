-- Prove2me | solution 2 for AvramDividend.Classical.chat04_interior_killed_discount_payoff_unmasked_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:53:58.979239+00:00
-- url     : https://prove2.me/submissions/442ec5fd-1ae1-46bd-a85e-52af6cd8b2d1

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
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

/-! At interior reserves the exact killed renewal payoff is initially unmasked. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x q : ℝ) (hx0 : 0 < x) (hxa : x < a)
    (W : ℝ → ℝ) (ω : Ω) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε →
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω =
          ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by
  obtain ⟨ε, hε, hsafe⟩ :=
    chat04_interior_two_sided_initial_safe_window X a x hx0 hxa ω
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hmem : ω ∈
      {u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u} := by
    intro s hs
    have hslt : s < ε := lt_of_le_of_lt hs ht
    have hlow := (hsafe s hslt).1
    linarith
  rw [Set.indicator_of_mem hmem]
