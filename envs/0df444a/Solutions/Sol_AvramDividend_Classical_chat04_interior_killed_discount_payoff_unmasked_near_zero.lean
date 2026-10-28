-- Prove2me | solution 1 for AvramDividend.Classical.chat04_interior_killed_discount_payoff_unmasked_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:53:52.942047+00:00
-- url     : https://prove2.me/submissions/e84232e0-96d2-452b-a260-57142e405383

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
  obtain ⟨ε, hε, h⟩ :=
    AvramDividend.Classical.chat04_interior_two_sided_initial_safe_window X a x hx0 hxa ω
  refine ⟨ε, hε, fun t ht => Set.indicator_of_mem ?_ _⟩
  intro s hs
  have := (h s (hs.trans_lt ht)).1
  linarith
