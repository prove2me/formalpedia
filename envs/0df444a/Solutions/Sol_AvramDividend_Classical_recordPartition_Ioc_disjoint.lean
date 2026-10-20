-- Prove2me | solution 1 for AvramDividend.Classical.recordPartition_Ioc_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:43:27.861877+00:00
-- url     : https://prove2.me/submissions/7ed22087-b61c-43f4-92d8-5417d85b8669

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.Set.Disjoint

open Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/- Ordered record-level cells (u_i, u_(i+1)] are disjoint. -/
theorem solution
    (u : ℕ → ℝ) (hu : Monotone u)
    (i j : ℕ) (hij : i < j) :
    Disjoint (Set.Ioc (u i) (u (i + 1)))
             (Set.Ioc (u j) (u (j + 1))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hstep : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
  have hLevel : u (i + 1) ≤ u j := hu hstep
  exact (not_lt_of_ge (le_trans hx.2 hLevel)) hy.1
