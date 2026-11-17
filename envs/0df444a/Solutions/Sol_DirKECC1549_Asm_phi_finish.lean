-- Prove2me | solution 1 for DirKECC1549.Asm.phi_finish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:47.626713+00:00
-- url     : https://prove2.me/submissions/a54d4cf5-c375-4696-87f1-eaef36055d67

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (rest po : List (Fin n)) (ptr : Fin n → ℕ) (v : Fin n)
    (hvr : v ∉ rest) (hvp : v ∉ po) (hp : ptr v = ots D (v + 1)) :
    Phi D rest (po ++ [v]) ptr = Phi D (rest ++ [v]) po ptr + 1 := by
  have e1 : (rest ++ [v]).toFinset = insert v rest.toFinset := by
    ext x; simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, mem_insert]; tauto
  have e2 : (po ++ [v]).toFinset = insert v po.toFinset := by
    ext x; simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, mem_insert]; tauto
  have hS1 : ∑ w ∈ insert v rest.toFinset, (ptr w - ots D w) =
      (ptr v - ots D v) + ∑ w ∈ rest.toFinset, (ptr w - ots D w) :=
    sum_insert (by simpa using hvr)
  have hS2 : ∑ w ∈ insert v po.toFinset, odeg D w = odeg D v + ∑ w ∈ po.toFinset, odeg D w :=
    sum_insert (by simpa using hvp)
  unfold Phi
  rw [e1, e2, hS1, hS2]
  simp only [List.length_append, List.length_singleton]
  unfold odeg
  rw [hp]
  ring
