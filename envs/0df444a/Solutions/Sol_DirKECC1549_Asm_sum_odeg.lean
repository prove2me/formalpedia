-- Prove2me | solution 1 for DirKECC1549.Asm.sum_odeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T07:05:04.457304+00:00
-- url     : https://prove2.me/submissions/4de945d3-7e84-42f8-b207-12bf08322ef5

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem ots_mono (D : Fin m → Fin n × Fin n) {a b : ℕ} (h : a ≤ b) : ots D a ≤ ots D b := by
  unfold ots; exact card_le_card (fun e => by simp only [mem_filter, mem_univ, true_and]; omega)

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : ∑ v ∈ S, odeg D v ≤ m := by
  have h1 : ∑ v ∈ S, odeg D v ≤ ∑ v : Fin n, odeg D v := sum_le_sum_of_subset (subset_univ S)
  have h2 : ∀ k ≤ n, ∑ v ∈ univ.filter (fun v : Fin n => (v : ℕ) < k), odeg D v = ots D k := by
    intro k hk
    induction k with
    | zero => simp [ots]
    | succ k ih =>
      rw [show univ.filter (fun v : Fin n => (v : ℕ) < k + 1) =
          insert ⟨k, by omega⟩ (univ.filter (fun v : Fin n => (v : ℕ) < k)) by
            ext v; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega,
        sum_insert (by simp), ih (by omega)]
      unfold odeg; simp only
      have := ots_mono D (show k ≤ k + 1 by omega)
      omega
  have h3 := h2 n le_rfl
  rw [show univ.filter (fun v : Fin n => (v : ℕ) < n) = univ by ext v; simp [v.isLt]] at h3
  have h4 : ots D n = m := by
    unfold ots; rw [filter_true_of_mem (fun e _ => (D e).1.isLt)]; simp
  omega
