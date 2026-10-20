-- Prove2me | solution 1 for AvramDividend.Classical.chat03_infinite_passage_discounted_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:31:30.201118+00:00
-- url     : https://prove2.me/submissions/50fcc94e-e6f7-4ac9-8cfe-231ebb61b676

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_terminal_bound
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
If neither official strict exit ever occurs, the reserve stays inside
the closed strip and the discounted q-scale value is pathwise bounded
by its upper-barrier value at all finite times.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a - x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    ∀ t : ℝ≥0,
      0 ≤ Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ∧
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ≤ W a := by
  have hNo := (chat03_no_grid_exit_when_both_passages_infinite
    X ω (-x) (a - x) hUp hDown).1
  intro t
  have hxy : 0 ≤ x + X.X t ω := by
    rcases not_or.mp (hNo t) with ⟨hlo, _⟩
    linarith
  have hxya : x + X.X t ω ≤ a := by
    rcases not_or.mp (hNo t) with ⟨_, hhi⟩
    linarith
  constructor
  · exact mul_nonneg (Real.exp_nonneg _) (hW.2.1 _ hxy)
  · have hb :=
      chat03_discounted_scale_terminal_bound
        X q hq W hW a (x + X.X t ω) hxy hxya 0 t (by exact zero_le)
    simpa using hb
