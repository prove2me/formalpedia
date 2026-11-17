-- Prove2me | solution 1 for DirKECC1549.Asm.phi_push
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:52.238145+00:00
-- url     : https://prove2.me/submissions/f6a2ca3a-7cd4-4e1a-903b-efc3a35328d5

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem sum_stk_update (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) (ptr : Fin n → ℕ)
    (v : Fin n) (hv : v ∈ S) (hlo : ots D v ≤ ptr v) :
    ∑ w ∈ S, (Function.update ptr v (ptr v + 1) w - ots D w) = ∑ w ∈ S, (ptr w - ots D w) + 1 := by
  rw [← add_sum_erase S _ hv, ← add_sum_erase S _ hv, Function.update_self]
  rw [sum_congr rfl (fun w hw => by rw [Function.update_of_ne (ne_of_mem_erase hw)])]
  omega

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (stk po : List (Fin n)) (ptr : Fin n → ℕ) (v t : Fin n)
    (hv : v ∈ stk) (ht : t ∉ stk) (hlo : ots D v ≤ ptr v) :
    Phi D (stk ++ [t]) po (Function.update (Function.update ptr v (ptr v + 1)) t (ots D t)) =
      Phi D stk po ptr + 2 := by
  have e1 : (stk ++ [t]).toFinset = insert t stk.toFinset := by
    ext x; simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, mem_insert]; tauto
  have hS : ∑ w ∈ insert t stk.toFinset,
      (Function.update (Function.update ptr v (ptr v + 1)) t (ots D t) w - ots D w) =
      ∑ w ∈ stk.toFinset, (ptr w - ots D w) + 1 := by
    rw [sum_insert (by simpa using ht), Function.update_self, Nat.sub_self, Nat.zero_add]
    rw [sum_congr rfl (fun w hw => by
      rw [Function.update_of_ne (by rintro rfl; exact ht (by simpa using hw))])]
    exact sum_stk_update D _ ptr v (by simpa using hv) hlo
  unfold Phi
  rw [e1, hS]
  simp only [List.length_append, List.length_singleton]
  ring
