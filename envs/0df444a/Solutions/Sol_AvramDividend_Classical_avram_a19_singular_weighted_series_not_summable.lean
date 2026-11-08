-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_weighted_series_not_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:30:38.246896+00:00
-- url     : https://prove2.me/submissions/77af47a0-a2c8-4e6c-9115-8ca9f8bc2c6b

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_power_cell_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A geometric-law source-cell generator loss has divergent absolute series. -/
theorem solution (y : Nat -> Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Summable (fun k : Nat =>
      (-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k)) := by
  intro hs
  have hle : forall k : Nat, (1 : Real) <=
      (-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k := by
    intro k
    have hbound :=
      AvramDividend.Classical.avram_a19_singular_power_cell_bound
        k (y k) (hy k) (hsmall k) (hpower k)
    have hp : 0 < (2 : Real) ^ k := pow_pos (by norm_num) _
    exact (le_div_iff₀ hp).2 (by nlinarith)
  have hsone : Summable (fun _ : Nat => (1 : Real)) :=
    Summable.of_nonneg_of_le (fun _ => by norm_num) hle hs
  have hzero : (1 : Real) = 0 :=
    (summable_const_iff (1 : Real)).1 hsone
  norm_num at hzero
