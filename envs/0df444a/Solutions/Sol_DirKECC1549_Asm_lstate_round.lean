-- Prove2me | solution 1 for DirKECC1549.Asm.lstate_round
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:50.557406+00:00
-- url     : https://prove2.me/submissions/555fef04-d391-4e12-be2d-a60e4a171c01

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

theorem sc_refl (D : Fin m → Fin n × Fin n) (a : Fin n) : StronglyConn D a a :=
  ⟨⟨[], IsWalk.nil a⟩, ⟨[], IsWalk.nil a⟩⟩

theorem sc_symm (D : Fin m → Fin n × Fin n) {a b : Fin n} (h : StronglyConn D a b) :
    StronglyConn D b a := ⟨h.2, h.1⟩

theorem sc_trans (D : Fin m → Fin n × Fin n) {a b c : Fin n} (h1 : StronglyConn D a b)
    (h2 : StronglyConn D b c) : StronglyConn D a c :=
  ⟨reach_trans D h1.1 h2.1, reach_trans D h2.2 h1.2⟩

/-! ## Strongly connected components -/

end DirKECC1549.Main.CostAux
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (A : Finset (Fin n)) (lab lab' : Fin n → ℕ) (c : ℕ)
    (hL : LState D A lab c) (v : Fin n) (hv : v ∉ A)
    (hlab : ∀ u, lab' u = if StronglyConn D v u then c else lab u) :
    LState D (A ∪ univ.filter (fun u => StronglyConn D v u)) lab' (c + 1) := by
  have hS : ∀ u ∈ A, ¬ StronglyConn D v u := fun u hu h => hv (hL.closed u v (sc_symm D h) hu)
  constructor
  · intro a b hab ha
    simp only [mem_union, mem_filter, mem_univ, true_and] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl (hL.closed a b hab ha)
    · exact Or.inr (sc_trans D ha hab)
  · intro a ha b hb
    simp only [mem_union, mem_filter, mem_univ, true_and] at ha hb
    rw [hlab a, hlab b]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [if_neg (hS a ha), if_neg (hS b hb)]; exact hL.iff a ha b hb
    · rw [if_neg (hS a ha), if_pos hb]
      constructor
      · intro h; have := hL.lt a ha; omega
      · intro h; exact absurd (sc_trans D hb (sc_symm D h)) (hS a ha)
    · rw [if_pos ha, if_neg (hS b hb)]
      constructor
      · intro h; have := hL.lt b hb; omega
      · intro h; exact absurd (sc_trans D ha h) (hS b hb)
    · rw [if_pos ha, if_pos hb]
      simp only [true_iff]
      exact sc_trans D (sc_symm D ha) hb
  · intro a ha
    simp only [mem_union, mem_filter, mem_univ, true_and] at ha
    rw [hlab a]
    rcases ha with ha | ha
    · rw [if_neg (hS a ha)]; have := hL.lt a ha; omega
    · rw [if_pos ha]; omega
  · intro j hj
    rcases Nat.lt_or_ge j c with h1 | h1
    · obtain ⟨a, ha, h2⟩ := hL.used j h1
      exact ⟨a, mem_union_left _ ha, by rw [hlab a, if_neg (hS a ha)]; exact h2⟩
    · exact ⟨v, by simp [sc_refl], by rw [hlab v, if_pos (sc_refl D v)]; omega⟩
  · have : (A ∪ univ.filter (fun u => StronglyConn D v u)).card = A.card +
        (univ.filter (fun u => StronglyConn D v u)).card := by
      apply card_union_of_disjoint
      rw [disjoint_left]; intro a ha hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact hS a ha hb
    have h2 : 0 < (univ.filter (fun u => StronglyConn D v u)).card :=
      card_pos.2 ⟨v, by simp [sc_refl]⟩
    have := hL.card
    omega
