-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_vanishing_width_halfopen_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:22:16.271197+00:00
-- url     : https://prove2.me/submissions/9082c69d-bc76-48ba-b339-dd44770472b6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- A shrinking half-open cell converges to its contained point from the
strict left and the weak right, with no grid-specific arithmetic needed. -/
theorem solution (u : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ n, a n < u ∧ u ≤ b n)
    (hwidth : Tendsto (fun n => b n - a n) atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto a atTop (𝓝[<] u) ∧
      Tendsto b atTop (nhdsWithin u (Ici u)) := by
  have hEq (n : ℕ) : b n = a n + (b n - a n) := by
    rw [add_comm]
    exact (tsub_add_cancel_of_le ((hab n).1.le.trans (hab n).2)).symm
  have hLower : ∀ n, u - (b n - a n) ≤ a n := by
    intro n
    apply (tsub_le_iff_right).2
    calc
      u ≤ b n := (hab n).2
      _ = a n + (b n - a n) := hEq n
  have hUpper : ∀ n, b n ≤ u + (b n - a n) := by
    intro n
    calc
      b n = a n + (b n - a n) := hEq n
      _ ≤ u + (b n - a n) := by
        gcongr <;> exact (hab n).1.le
  have hSub : Tendsto (fun n => u - (b n - a n)) atTop (𝓝 u) := by
    simpa only [tsub_zero] using
      (tendsto_const_nhds.sub hwidth :
        Tendsto (fun n => u - (b n - a n)) atTop (𝓝 (u - 0)))
  have hAdd : Tendsto (fun n => u + (b n - a n)) atTop (𝓝 u) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hwidth :
        Tendsto (fun n => u + (b n - a n)) atTop (𝓝 (u + 0)))
  have ha : Tendsto a atTop (𝓝 u) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hSub tendsto_const_nhds hLower (fun n => (hab n).1.le)
  have hb : Tendsto b atTop (𝓝 u) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hAdd (fun n => (hab n).2) hUpper
  constructor
  · exact tendsto_nhdsWithin_iff.mpr
      ⟨ha, Filter.Eventually.of_forall (fun n => (hab n).1)⟩
  · exact tendsto_nhdsWithin_iff.mpr
      ⟨hb, Filter.Eventually.of_forall (fun n => (hab n).2)⟩
