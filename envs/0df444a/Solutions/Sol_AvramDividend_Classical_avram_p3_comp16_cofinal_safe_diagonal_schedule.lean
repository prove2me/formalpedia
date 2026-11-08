-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp16_cofinal_safe_diagonal_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:47:17.963925+00:00
-- url     : https://prove2.me/submissions/b5dede59-a7f5-4e16-81af-cff1e51e5b91

import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
noncomputable section

theorem solution
    (N : ℕ → ℕ) (hN0 : N 0 = 0)
    (hNge : ∀ k, k ≤ N k) :
    ∃ κ : ℕ → ℕ,
      (∀ n, κ n ≤ n) ∧
      (∀ n, N (κ n) ≤ n) ∧
      Tendsto κ atTop atTop := by
  classical
  let κ : ℕ → ℕ := fun n =>
    Nat.findGreatest (fun k => N k ≤ n) n
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro n
    exact Nat.findGreatest_le n
  · intro n
    dsimp [κ]
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n)
      (m := 0) (Nat.zero_le n)
      (by simpa [hN0] using (Nat.zero_le n))
  · apply Filter.tendsto_atTop.2
    intro k
    filter_upwards [Filter.eventually_ge_atTop (N k)] with n hn
    exact Nat.le_findGreatest (le_trans (hNge k) hn) hn
