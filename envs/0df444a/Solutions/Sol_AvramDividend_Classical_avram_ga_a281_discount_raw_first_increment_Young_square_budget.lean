-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a281_discount_raw_first_increment_Young_square_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:31:22.224307+00:00
-- url     : https://prove2.me/submissions/7c9c1d61-0707-44c0-be56-92c95a37b002

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (η Q L r : ℝ) (hη : 0 < η)
    (hQ : 0 ≤ Q) (hL : 0 ≤ L) :
    Q*L*|r| ≤ η*r^2+(Q*L)^2/(4*η) := by
  have hfour : (0:ℝ) < 4*η := by positivity
  have heq : (2*η*|r|-Q*L)^2 =
      4*η^2*r^2-4*η*Q*L*|r|+(Q*L)^2 := by
    rw [← sq_abs r]
    ring
  have hsq := sq_nonneg (2*η*|r|-Q*L)
  rw [heq] at hsq
  have hbound : Q*L*|r|-η*r^2 ≤ (Q*L)^2/(4*η) := by
    apply (le_div_iff₀ hfour).2
    nlinarith
  linarith
