-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_barrier_ruin_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:38:16.009021+00:00
-- url     : https://prove2.me/submissions/615e4859-46aa-495c-bcc1-3a340b610c28

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_piecewise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω) :
    riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
      (runningSup X t ω < a - x ∧ X.X t ω < -x) ∨
      (a - x ≤ runningSup X t ω ∧
        a < runningSup X t ω - X.X t ω) := by
  rw [riskProcess_barrier_piecewise X x a hxa t ht ω]
  by_cases hb : runningSup X t ω < a - x
  · rw [if_pos hb]
    constructor
    · intro hruin
      left
      constructor
      · exact hb
      · linarith
    · rintro (⟨_, hx⟩ | ⟨hge, _⟩)
      · linarith
      · exact False.elim ((not_le_of_gt hb) hge)
  · rw [if_neg hb]
    have hge : a - x ≤ runningSup X t ω := le_of_not_gt hb
    constructor
    · intro hruin
      right
      exact ⟨hge, by linarith⟩
    · rintro (⟨hbelow, _⟩ | ⟨_, hdraw⟩)
      · exact False.elim (hb hbelow)
      · linarith
