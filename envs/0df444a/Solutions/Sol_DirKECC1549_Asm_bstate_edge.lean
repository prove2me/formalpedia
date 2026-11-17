-- Prove2me | solution 1 for DirKECC1549.Asm.bstate_edge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:45.377208+00:00
-- url     : https://prove2.me/submissions/031b7d98-e93a-4ceb-bc17-bf9909926d37

import Definitions.Def_DirKECC1549_Impl_SccBfs

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Main.CostAux

open DirKECC1549.Main

/-! ## Exponents -/

/-! ## Powers of `n` -/

/-! ## Combinatorial constants -/

/-! ## Walks and cuts -/

variable {n m : ℕ}

theorem walk_append (D : Fin m → Fin n × Fin n) {a b c : Fin n} {p q : List (Fin m)}
    (hp : IsWalk D a p b) (hq : IsWalk D b q c) : IsWalk D a (p ++ q) c := by
  induction hp with
  | nil => simpa using hq
  | cons e p he _ ih => exact IsWalk.cons e (p ++ q) he (ih hq)

theorem reach_trans (D : Fin m → Fin n × Fin n) {a b c : Fin n} (h1 : Reach D a b)
    (h2 : Reach D b c) : Reach D a c := by
  obtain ⟨p, hp⟩ := h1; obtain ⟨q, hq⟩ := h2; exact ⟨p ++ q, walk_append D hp hq⟩

/-! ## Strongly connected components -/

end DirKECC1549.Main.CostAux
end

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem reach_edge (D : Fin m → Fin n × Fin n) (e : Fin m) : Reach D (D e).1 (D e).2 :=
  ⟨[e], IsWalk.cons e [] rfl (IsWalk.nil _)⟩

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
    (q : List (Fin n)) (h : ℕ) (hB : BState D A v q h) (hh : h < q.length) (j : Fin m)
    (hj1 : its D (q[h]) ≤ j) (hj2 : (j : ℕ) < its D (q[h] + 1)) (hP : BPart D τ A q q[h] j) :
    let y := (D (τ j)).1
    (y ∉ A → y ∉ q → BState D A v (q ++ [y]) h ∧ BPart D τ A (q ++ [y]) q[h] (j + 1)) ∧
    (y ∈ A ∨ y ∈ q → BPart D τ A q q[h] (j + 1)) := by
  intro y
  have hhd : (D (τ j)).2 = q[h] := (head_of_pos D τ hτ q[h] j).2 ⟨hj1, hj2⟩
  refine ⟨fun hyA hyq => ⟨?_, ?_⟩, fun hy => ?_⟩
  · exact
    { nd := List.nodup_append.2 ⟨hB.nd, List.nodup_singleton y, by
        intro a ha b hb hab; simp at hb; subst hb; subst hab; exact hyq ha⟩
      hd := ⟨by simp, by
        obtain ⟨h1, h2⟩ := hB.hd
        cases q with
        | nil => exact absurd rfl h1
        | cons a q => simpa using h2⟩
      disj := fun u hu => by
        simp only [List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact hB.disj u hu
        · exact hyA
      reach := fun u hu => by
        simp only [List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact hB.reach u hu
        · exact reach_trans D (reach_edge D (τ j)) (by rw [hhd]; exact hB.reach _ (List.getElem_mem hh))
      hle := by simp; omega
      closed := fun i hi e he => by
        rw [List.getElem_append_left (by omega)] at he
        rcases hB.closed i hi e he with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_append_left _ h1) }
  · intro j' h1 h2
    rcases Nat.lt_or_ge (j' : ℕ) j with h3 | h3
    · rcases hP j' h1 h3 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr (List.mem_append_left _ h4)
    · have : j' = j := Fin.ext (by omega)
      subst this; exact Or.inr (by simp [y])
  · intro j' h1 h2
    rcases Nat.lt_or_ge (j' : ℕ) j with h3 | h3
    · exact hP j' h1 h3
    · have : j' = j := Fin.ext (by omega)
      subst this; exact hy
