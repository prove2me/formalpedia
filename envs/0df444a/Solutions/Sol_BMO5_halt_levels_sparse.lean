-- Prove2me | solution 1 for BMO5.halt_levels_sparse
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T17:26:53.635546+00:00
-- url     : https://prove2.me/submissions/ed06f82e-5e9c-4a1c-a8b5-be48cfb57975

import Mathlib
import Theorems.Thm_BMO5_adm_of_halt
import Theorems.Thm_BMO5_adm_periodic
import Theorems.Thm_BMO5_adm_count

theorem solution (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ D, ∃ S : Finset ℕ, S.card ≤ 2 ^ (D + 1) ∧ ∃ i0, ∀ n, b n = 10 * 2 ^ (a n) - 2 → i0 ≤ a n →
      a n % (2 * 3 ^ D) ∈ S := by
  intro D
  refine ⟨((Finset.range (2 * 3 ^ D)).filter (fun r => BMO5Adm.adm D (r + 2 * 3 ^ D * (D + 1)) = true)), BMO5.adm_count D, ?_⟩
  obtain ⟨i0, h0⟩ := BMO5.adm_of_halt a b a_ini b_ini a_rec b_rec D
  refine ⟨max i0 (D + 1), fun n hb hn => ?_⟩
  have hM : 0 < 2 * 3 ^ D := by positivity
  have hle : D + 1 ≤ 2 * 3 ^ D * (D + 1) := Nat.le_mul_of_pos_left _ hM
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ hM, ?_⟩
  rw [BMO5.adm_periodic D (a n % (2 * 3 ^ D) + 2 * 3 ^ D * (D + 1)) (a n) (by omega)
    (le_trans (le_max_right _ _) hn) (by rw [Nat.add_mul_mod_self_left, Nat.mod_mod])]
  exact h0 n hb (le_trans (le_max_left _ _) hn)
