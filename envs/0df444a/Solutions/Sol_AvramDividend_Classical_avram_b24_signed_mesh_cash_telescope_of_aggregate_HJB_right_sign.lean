-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_signed_mesh_cash_telescope_of_aggregate_HJB_right_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:15:45.444043+00:00
-- url     : https://prove2.me/submissions/b4c7aa39-5e94-4f60-ab6e-02483e378913

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem solution
    (N : ℕ) (w0 cash0 : ℝ)
    (V cash gaussian jump drift error : ℕ → ℝ)
    (hInitial : V 0 + cash0 ≤ w0)
    (hCell : ∀ i, i < N →
      V (i + 1) + cash i ≤
        V i + gaussian i + jump i + drift i + error i)
    (hTotal : (∑ i ∈ Finset.range N, drift i) ≤ 0) :
    V N + cash0 + (∑ i ∈ Finset.range N, cash i) ≤
      w0 + (∑ i ∈ Finset.range N, gaussian i) +
        (∑ i ∈ Finset.range N, jump i) +
        (∑ i ∈ Finset.range N, error i) := by
  have hClaim : ∀ n : ℕ,
      (∀ i, i < n →
        V (i + 1) + cash i ≤
          V i + gaussian i + jump i + drift i + error i) →
      V n + cash0 + (∑ i ∈ Finset.range n, cash i) ≤
        w0 + (∑ i ∈ Finset.range n, gaussian i) +
          (∑ i ∈ Finset.range n, jump i) +
          (∑ i ∈ Finset.range n, drift i) +
          (∑ i ∈ Finset.range n, error i) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using hInitial
    | succ n ih =>
        intro hn
        have hprev := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
        have hlast := hn n (Nat.lt_succ_self n)
        simp only [Finset.sum_range_succ]
        linarith
  have hAll := hClaim N hCell
  linarith
