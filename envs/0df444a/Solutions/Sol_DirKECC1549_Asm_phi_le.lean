-- Prove2me | solution 1 for DirKECC1549.Asm.phi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:49.375195+00:00
-- url     : https://prove2.me/submissions/89aa738d-1029-4c4b-9881-65e7306c8945

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

theorem sum_odeg (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : ∑ v ∈ S, odeg D v ≤ m := by
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

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (stk po : List (Fin n))
    (ptr : Fin n → ℕ) (h : DState D σ stk po ptr) : Phi D stk po ptr ≤ 2 * n + m := by
  unfold Phi
  have hl : stk.length + po.length ≤ n := by
    have := h.nd.length_le_card
    simpa using this
  have hd : Disjoint stk.toFinset po.toFinset := by
    rw [disjoint_left]; intro a ha hb
    simp only [List.mem_toFinset] at ha hb
    exact (List.nodup_append.1 h.nd).2.2 a ha a hb rfl
  have h1 : ∑ v ∈ stk.toFinset, (ptr v - ots D v) ≤ ∑ v ∈ stk.toFinset, odeg D v :=
    sum_le_sum (fun v hv => by
      unfold odeg; have := h.phi v (by simpa using hv); omega)
  have h2 := sum_odeg D (stk.toFinset ∪ po.toFinset)
  rw [sum_union hd] at h2
  omega
