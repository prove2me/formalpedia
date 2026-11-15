-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB61_finite_mesh_postpayment_potential_cash_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:51:06.503101+00:00
-- url     : https://prove2.me/submissions/2a3dc826-739f-40a2-a1d3-da972aadaeb5

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem solution
    (Y Z Cash : ℕ → ℝ) (initial U : ℝ) (n : ℕ)
    (hCash :
      initial + Y 0 +
        (Finset.sum (Finset.range n) (fun i =>
          Cash i + Y (i + 1) - Z i)) ≤ U) :
    initial + Y n + (Finset.sum (Finset.range n) (fun i => Cash i)) ≤
      U + (Finset.sum (Finset.range n) (fun i => Z i - Y i)) := by
  have hTel : ∀ k : ℕ,
      Y 0 + (Finset.sum (Finset.range k) (fun i =>
        Cash i + Y (i + 1) - Z i)) +
      (Finset.sum (Finset.range k) (fun i => Z i - Y i)) =
        Y k + (Finset.sum (Finset.range k) (fun i => Cash i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      linarith
  have h := hTel n
  linarith
