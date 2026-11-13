-- Prove2me | solution 1 for AvramDividend.Classical.avram_b21_ruinclipped_signed_mesh_cash_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:48:49.175008+00:00
-- url     : https://prove2.me/submissions/483e7e27-6cf0-4ff8-a1bc-e659ee4a118b

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Aggregate a ruin-masked stopped mesh; include the time-zero right dividend and drop nonpositive HJB drift. -/
theorem solution
    (N : Nat) (w0 cash0 : Real)
    (V cash gaussian jump drift error : Nat -> Real)
    (hInitial : V 0 + cash0 <= w0)
    (hCell : forall i, i < N ->
      V (i + 1) + cash i <=
        V i + gaussian i + jump i + drift i + error i)
    (hDrift : forall i, i < N -> drift i <= 0) :
    V N + cash0 + (Finset.range N).sum cash <=
      w0 + (Finset.range N).sum gaussian +
        (Finset.range N).sum jump +
        (Finset.range N).sum error := by
  have hTelescope : forall n : Nat, n <= N ->
      V n + (Finset.range n).sum cash <=
        V 0 + (Finset.range n).sum gaussian +
          (Finset.range n).sum jump +
          (Finset.range n).sum drift +
          (Finset.range n).sum error := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hBound : n < N := by omega
        have hPrevious := ih (by omega)
        have hStep := hCell n hBound
        simp only [Finset.sum_range_succ]
        linarith
  have hDriftTotal : (Finset.range N).sum drift <= (0 : Real) := by
    apply Finset.sum_nonpos
    intro i hi
    exact hDrift i (Finset.mem_range.mp hi)
  have hMain := hTelescope N le_rfl
  linarith
