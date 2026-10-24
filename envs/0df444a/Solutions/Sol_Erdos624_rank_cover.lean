-- Prove2me | solution 1 for Erdos624.rank_cover
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:49.642042+00:00
-- url     : https://prove2.me/submissions/b5642a61-c728-4e93-a1a5-2fb960557294

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624R4
open Finset

theorem rank_cover (r n k : ℕ) (hn : 0 < n) (h : n ≤ r * (k + 1)) :
    ∃ g : Fin r → Finset (Fin n) → Fin n,
      ∀ Y : Finset (Fin n), #Y = k → ∀ u : Fin n, ∃ i, ∃ A ⊆ Y, g i A = u := by
  refine ⟨fun i A => if hA : i.val * (k + 1) + #A < n then ⟨_, hA⟩ else ⟨0, hn⟩, ?_⟩
  intro Y hY u
  have hi : u.val / (k + 1) < r := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le u.isLt h
  have hmod : u.val % (k + 1) ≤ #Y := by
    rw [hY]; exact Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega))
  obtain ⟨A, hAY, hA⟩ := exists_subset_card_eq hmod
  refine ⟨⟨_, hi⟩, A, hAY, ?_⟩
  have he : u.val / (k + 1) * (k + 1) + #A = u.val := by rw [hA]; exact Nat.div_add_mod' _ _
  have hlt : u.val / (k + 1) * (k + 1) + #A < n := by rw [he]; exact u.isLt
  simp only [dif_pos hlt]
  exact Fin.ext he

/-- The pair common-hole claim fails at `k = 3`, `n = 2^3`. -/
theorem pair_common_hole_false_k3 :
    ¬ ∀ g : Fin 2 → Finset (Fin (2 ^ 3)) → Fin (2 ^ 3),
      ∃ Y : Finset (Fin (2 ^ 3)), #Y = 3 ∧ ∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u := by
  intro hall
  obtain ⟨g, hg⟩ := rank_cover 2 (2 ^ 3) 3 (by norm_num) (by norm_num)
  obtain ⟨Y, hY, u, hu⟩ := hall g
  obtain ⟨i, A, hA, he⟩ := hg Y hY u
  exact hu i A hA he

end E624R4


namespace Erdos624

theorem rank_cover (r n k : ℕ) (hn : 0 < n) (h : n ≤ r * (k + 1)) :
    ∃ g : Fin r → Finset (Fin n) → Fin n,
      ∀ Y : Finset (Fin n), #Y = k → ∀ u : Fin n, ∃ i, ∃ A ⊆ Y, g i A = u :=
  E624R4.rank_cover r n k hn h

end Erdos624

open Erdos624 in
theorem solution (r n k : ℕ) (hn : 0 < n) (h : n ≤ r * (k + 1)) :
    ∃ g : Fin r → Finset (Fin n) → Fin n,
      ∀ Y : Finset (Fin n), #Y = k → ∀ u : Fin n, ∃ i, ∃ A ⊆ Y, g i A = u :=
  Erdos624.rank_cover r n k hn h

#print axioms solution
