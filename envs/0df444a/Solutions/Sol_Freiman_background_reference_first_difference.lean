-- Prove2me | solution 1 for Freiman.background_reference_first_difference
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:53.574544+00:00
-- url     : https://prove2.me/submissions/8b6d6a62-0374-4d23-be60-ff1530a6f504

import Theorems.Thm_Freiman_background_reference_cycles
import Theorems.Thm_Freiman_background_first_difference_candidate
import Theorems.Thm_Freiman_background_phase_policy

open Freiman

theorem solution (r : Bool) (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4])
    (ha : BackgroundAllowed (backgroundReferenceState r) b)
    (n : ℕ) (hp : ∀ k : ℕ, k < n → b k = backgroundReference r k)
    (hd : b n ≠ backgroundReference r n) :
    if Even n then backgroundReference r n < b n else b n < backgroundReference r n := by
  have hc := background_first_difference_candidate r b hb h14 ha n hp
    (background_reference_cycles r n)
  have hle := background_phase_policy r n (b n) hc
  by_cases hn : Even n
  · simp only [hn, if_pos] at hle ⊢
    exact lt_of_le_of_ne hle hd.symm
  · simp only [hn] at hle ⊢
    exact lt_of_le_of_ne hle hd
