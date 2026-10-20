-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_integer_horizon_terminal_scale_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:54:46.362566+00:00
-- url     : https://prove2.me/submissions/92fb0fec-2ec0-4606-8ce3-214f1d20d2e0

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat04_bounded_strip_scale_terminal_vanish
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
On a sample path with both named strict first passage times infinite,
the discounted scale payoff vanishes along deterministic integer
horizons. This uses an accepted bounded-strip terminal-limit theorem.
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
    Tendsto (fun n : ℕ =>
      Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
      atTop (𝓝 0) := by
  have hNo := (chat03_no_grid_exit_when_both_passages_infinite
    X ω (-x) (a - x) hUp hDown).1
  have hstrip : ∀ n : ℕ,
      0 ≤ x + X.X (n : ℝ≥0) ω ∧ x + X.X (n : ℝ≥0) ω ≤ a := by
    intro n
    obtain ⟨hlo, hhi⟩ := not_or.mp (hNo (n : ℝ≥0))
    constructor <;> linarith
  exact chat04_bounded_strip_scale_terminal_vanish X q hq W hW a
    (fun n : ℕ => x + X.X (n : ℝ≥0) ω) hstrip
