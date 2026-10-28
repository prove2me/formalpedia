-- Prove2me | solution 1 for AvramDividend.Classical.chat04_interior_two_sided_exit_clocks_pos_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:42:36.499605+00:00
-- url     : https://prove2.me/submissions/4f3a661b-dbaa-4060-8f12-5484738c1c74

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_pos_of_initial_safe_ceiling
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (hx0 : 0 < x) (hxa : x < a) :
    ∀ᵐ ω ∂P,
      0 < twoSidedExitUpTime X (a - x) ω ∧
      0 < twoSidedExitDownTime X (-x) ω := by
  refine Filter.Eventually.of_forall fun ω => ?_
  obtain ⟨ε, hε, h⟩ :=
    AvramDividend.Classical.chat04_interior_two_sided_initial_safe_window X a x hx0 hxa ω
  exact ⟨AvramDividend.Classical.chat04_up_exit_time_pos_of_initial_safe_ceiling X (a - x) ω ε hε
      fun t ht => (h t ht).2,
    AvramDividend.Classical.chat04_down_exit_time_pos_of_initial_safe_window X x ω ε hε
      fun t ht => (h t ht).1⟩
