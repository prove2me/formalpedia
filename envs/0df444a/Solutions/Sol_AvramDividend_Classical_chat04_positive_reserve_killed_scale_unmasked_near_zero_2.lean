-- Prove2me | solution 2 for AvramDividend.Classical.chat04_positive_reserve_killed_scale_unmasked_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:58:19.013782+00:00
-- url     : https://prove2.me/submissions/d63436e5-643e-4bf3-b966-d42d7ef9de2f

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
  obtain ⟨ε, hε, h⟩ :=
    AvramDividend.Classical.chat04_initial_safe_window_of_rightCont_zero X x hx ω (X.X_zero ω)
  refine ⟨ε, hε, fun t ht => Set.indicator_of_mem ?_ _⟩
  intro s hs
  have := h s (hs.trans_lt ht)
  linarith
