-- Prove2me | solution 1 for Erdos287.distinct_cofactor_intervals_form_chain
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:23:22.18641+00:00
-- url     : https://prove2.me/submissions/eacd61bb-d12b-449e-ae99-b6f517f7276c

import Mathlib

open Finset

set_option autoImplicit false

/-- In one denominator interval, the cofactor endpoints move together as
the divisor changes. Their sum encodes each distinct endpoint pair. -/
theorem solution (P : Finset ℕ) (m M B : ℕ) (hmM : m ≤ M)
    (hP : ∀ p ∈ P, 0 < p ∧ M / p ≤ B) :
    (P.image (fun p => ((m - 1) / p + 1, M / p))).card ≤ 2 * B + 1 := by
  let a (p : ℕ) := (m - 1) / p + 1
  let b (p : ℕ) := M / p
  let S := P.image (fun p => (a p, b p))
  let code (x : ℕ × ℕ) := x.1 + x.2
  have hmap : Set.MapsTo code (↑S : Set (ℕ × ℕ)) (↑(Icc 1 (2 * B + 1)) : Set ℕ) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (show x ∈ S from hx)
    have hb : b p ≤ B := (hP p hp).2
    have ha : a p ≤ B + 1 := Nat.succ_le_succ
      ((Nat.div_le_div_right (show m - 1 ≤ M by omega)).trans hb)
    have hapos : 1 ≤ a p := Nat.succ_le_succ (Nat.zero_le _)
    apply mem_Icc.mpr
    change 1 ≤ a p + b p ∧ a p + b p ≤ 2 * B + 1
    omega
  have hmono (p q : ℕ) (hp : p ∈ P) (hpq : p ≤ q) :
      a q ≤ a p ∧ b q ≤ b p :=
    ⟨Nat.succ_le_succ (Nat.div_le_div_left hpq (hP p hp).1),
      Nat.div_le_div_left hpq (hP p hp).1⟩
  have hinj : Set.InjOn code (↑S : Set (ℕ × ℕ)) := by
    intro x hx y hy he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (show x ∈ S from hx)
    obtain ⟨q, hq, rfl⟩ := mem_image.mp (show y ∈ S from hy)
    change a p + b p = a q + b q at he
    rcases le_total p q with h | h
    · obtain ⟨ha, hb⟩ := hmono p q hp h
      exact Prod.ext (by change a p = a q; omega) (by change b p = b q; omega)
    · obtain ⟨ha, hb⟩ := hmono q p hq h
      exact Prod.ext (by change a p = a q; omega) (by change b p = b q; omega)
  have hc := card_le_card_of_injOn code hmap hinj
  simpa [S, a, b] using hc

