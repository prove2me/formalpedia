-- Prove2me | solution 1 for Freiman.cfValue_le_of_first_difference
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:30:05.136996+00:00
-- url     : https://prove2.me/submissions/88aeac0f-c702-435b-b581-ccb8a7e642d5

import Theorems.Thm_Freiman_gap_tail_first_difference

open Freiman

theorem solution (b c : ℕ → ℕ+)
    (h : ∀ n : ℕ, (∀ k : ℕ, k < n → b k = c k) → b n ≠ c n →
      if Even n then c n < b n else b n < c n) :
    cfValue b ≤ cfValue c := by
  classical
  by_cases heq : b = c
  · simp [heq]
  have hex : ∃ n : ℕ, b n ≠ c n := by
    by_contra hx
    apply heq
    funext n
    by_contra hn
    exact hx ⟨n, hn⟩
  let n := Nat.find hex
  have hd : b n ≠ c n := Nat.find_spec hex
  have hp : ∀ k : ℕ, k < n → b k = c k := by
    intro k hk
    by_contra hneq
    exact (Nat.not_le_of_gt hk) (Nat.find_min' hex hneq)
  exact ((gap_tail_first_difference b c n hp hd).2 (h n hp hd)).le

