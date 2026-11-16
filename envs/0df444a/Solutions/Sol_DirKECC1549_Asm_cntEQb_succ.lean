-- Prove2me | solution 1 for DirKECC1549.Asm.cntEQb_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T04:00:15.226567+00:00
-- url     : https://prove2.me/submissions/a5ff7802-7b57-4681-bf81-569a70a0c834

import Definitions.Def_DirKECC1549_Impl_LayComb

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset
open DirKECC1549 DirKECC1549.Asm
variable {m : ℕ}

theorem solution (key : Fin m → ℕ) (j : ℕ) (hj : j < m) (v : ℕ) :
    cntEQb key (j + 1) v = cntEQb key j v + if key ⟨j, hj⟩ = v then 1 else 0 := by
  unfold cntEQb
  split_ifs with h
  · rw [show univ.filter (fun e : Fin m => (e : ℕ) < j + 1 ∧ key e = v) =
        insert ⟨j, hj⟩ (univ.filter (fun e : Fin m => (e : ℕ) < j ∧ key e = v)) by
          ext e; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          constructor
          · rintro ⟨h1, h2⟩; rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl h1
          · rintro (h1 | ⟨h1, h2⟩)
            · refine ⟨by omega, ?_⟩
              have : e = ⟨j, hj⟩ := Fin.ext h1
              rw [this]; exact h
            · exact ⟨by omega, h2⟩]
    rw [card_insert_of_notMem (by simp)]
  · simp only [add_zero]; apply congrArg Finset.card; ext e; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
      · exact h1
      · exact absurd (by rw [← h2]; congr 1; exact Fin.ext h1.symm) h
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
