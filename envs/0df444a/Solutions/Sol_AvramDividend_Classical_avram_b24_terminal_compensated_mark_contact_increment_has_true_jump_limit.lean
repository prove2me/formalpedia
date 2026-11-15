-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:01:29.529974+00:00
-- url     : https://prove2.me/submissions/f8e006f2-f3d4-43a5-be85-0d920178213e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (J : ℝ≥0 → ℝ) (t : ℝ≥0) (Jleft : ℝ)
    (a b : ℕ → ℝ≥0) (W : ℕ → ℝ) (Wleft : ℝ)
    (hRight : ContinuousWithinAt J (Ici t) t)
    (hLeft : Tendsto J (𝓝[<] t) (𝓝 Jleft))
    (ha : Tendsto a atTop (𝓝[<] t))
    (hb : Tendsto b atTop (𝓝[Ici t] t))
    (hW : Tendsto W atTop (𝓝 Wleft)) :
    Tendsto (fun k => W k * (J (b k) - J (a k))) atTop
      (𝓝 (Wleft * (J t - Jleft))) := by
  have hB : Tendsto (fun k => J (b k)) atTop (𝓝 (J t)) :=
    hRight.tendsto.comp hb
  have hA : Tendsto (fun k => J (a k)) atTop (𝓝 Jleft) :=
    hLeft.comp ha
  exact hW.mul (hB.sub hA)
