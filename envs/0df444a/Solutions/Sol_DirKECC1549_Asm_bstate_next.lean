-- Prove2me | solution 1 for DirKECC1549.Asm.bstate_next
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:53.268888+00:00
-- url     : https://prove2.me/submissions/12947e71-66f9-4589-8379-f50af89946de

import Definitions.Def_DirKECC1549_Impl_SccBfs

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

end DirKECC1549.Asm

namespace DirKECC1549.Asm

/-- A down-closed set of positions of size `c` is `{i < c}`. -/
theorem downset_iff {m : ℕ} (S : Finset (Fin m)) (hS : ∀ i j : Fin m, j ≤ i → i ∈ S → j ∈ S)
    (i : Fin m) : i ∈ S ↔ (i : ℕ) < S.card := by
  constructor
  · intro hi
    have : (univ.filter (fun j : Fin m => j ≤ i)) ⊆ S := fun j hj => hS i j (by simpa using hj) hi
    have h2 := card_le_card this
    have h3 : (univ.filter (fun j : Fin m => j ≤ i)).card = i + 1 := by
      rw [show univ.filter (fun j : Fin m => j ≤ i) = Iic i by ext; simp]
      simp
    omega
  · intro hi
    by_contra hni
    have : S ⊆ univ.filter (fun j : Fin m => j < i) := fun j hj => by
      simp only [mem_filter, mem_univ, true_and]
      by_contra h
      exact hni (hS j i (not_lt.1 h) hj)
    have h2 := card_le_card this
    have h3 : (univ.filter (fun j : Fin m => j < i)).card = i := by
      rw [show univ.filter (fun j : Fin m => j < i) = Iio i by ext; simp]
      simp
    omega

/-- In a key-sorted permutation, the positions with key below `v` are the first
`#{e : key e < v}`. -/
theorem sorted_prefix {m : ℕ} (κ : Fin m → ℕ) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => κ (σ i))) (v : ℕ) (i : Fin m) :
    κ (σ i) < v ↔ (i : ℕ) < (univ.filter (fun e => κ e < v)).card := by
  have hc : (univ.filter (fun i : Fin m => κ (σ i) < v)).card = (univ.filter (fun e => κ e < v)).card := by
    apply card_bij (fun i _ => σ i)
    · intro a ha; simpa using ha
    · intro a _ b _ h; exact σ.injective h
    · intro b hb; exact ⟨σ.symm b, by simpa using hb, by simp⟩
  rw [← hc]
  have := downset_iff (univ.filter (fun i : Fin m => κ (σ i) < v))
    (fun i j hji hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact lt_of_le_of_lt (hσ hji) hi) i
  simpa using this

/-- The edges at sorted positions `[#{κ < v}, #{κ < v+1})` are exactly those with key `v`. -/
theorem sorted_block {m : ℕ} (κ : Fin m → ℕ) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => κ (σ i))) (v : ℕ) (i : Fin m) :
    κ (σ i) = v ↔ (univ.filter (fun e => κ e < v)).card ≤ (i : ℕ) ∧
      (i : ℕ) < (univ.filter (fun e => κ e < v + 1)).card := by
  rw [← sorted_prefix κ σ hσ (v + 1), ← not_lt, ← sorted_prefix κ σ hσ v]
  omega

end DirKECC1549.Asm
end

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem head_of_pos (D : Fin m → Fin n × Fin n) (τ : Equiv.Perm (Fin m))
    (hτ : Monotone (fun i => ((D (τ i)).2 : ℕ))) (v : Fin n) (i : Fin m) :
    (D (τ i)).2 = v ↔ its D v ≤ i ∧ (i : ℕ) < its D (v + 1) := by
  have h := sorted_block (fun e => ((D e).2 : ℕ)) τ hτ v i
  unfold its; rw [Fin.ext_iff]; exact h

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (τ : Equiv.Perm (Fin m))
    (hτ : Monotone (fun i => ((D (τ i)).2 : ℕ))) (A : Finset (Fin n)) (v : Fin n)
    (q : List (Fin n)) (h : ℕ) (hB : BState D A v q h) (hh : h < q.length)
    (hP : BPart D τ A q q[h] (its D (q[h] + 1))) : BState D A v q (h + 1) where
  nd := hB.nd
  hd := hB.hd
  disj := hB.disj
  reach := hB.reach
  hle := by omega
  closed := fun i hi e he => by
    rcases Nat.lt_or_ge i h with h1 | h1
    · exact hB.closed i h1 e he
    · have : i = h := by omega
      subst this
      have h2 : (D (τ (τ.symm e))).2 = q[i] := by simpa using he
      obtain ⟨a1, a2⟩ := (head_of_pos D τ hτ _ _).1 h2
      simpa using hP (τ.symm e) a1 a2
