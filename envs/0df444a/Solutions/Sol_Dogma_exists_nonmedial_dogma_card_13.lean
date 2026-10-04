-- Prove2me | solution 1 for Dogma.exists_nonmedial_dogma_card_13
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:53:07.121984+00:00
-- url     : https://prove2.me/submissions/709ea191-98c6-4184-932c-a56e6ee104dc

import Mathlib

set_option autoImplicit false

namespace DogmaCay

/-- The translation-invariant operation `x ⋆ y = y + f (x - y)`. -/
def cstar {G : Type} [AddCommGroup G] (f : G → G) (x y : G) : G := y + f (x - y)

lemma cstar_rc {G : Type} [AddCommGroup G] (f : G → G) (hf : Function.Injective f)
    (x y z : G) (h : cstar f x z = cstar f y z) : x = y := by
  unfold cstar at h
  have h1 : f (x - z) = f (y - z) := add_left_cancel h
  have h2 := hf h1
  exact sub_left_inj.mp h2

lemma cstar_id {G : Type} [AddCommGroup G] (f : G → G) (hf : ∀ t, f (f t) = t + f (-t))
    (x y : G) : cstar f (cstar f x y) y = cstar f y x := by
  unfold cstar
  have h1 : y + f (x - y) - y = f (x - y) := by abel
  rw [h1, hf (x - y)]
  have h2 : -(x - y) = y - x := by abel
  rw [h2]
  abel

def f13 (t : ZMod 13) : ZMod 13 :=
  ([0, 9, 8, 1, 5, 7, 11, 4, 12, 3, 6, 10, 2] : List (ZMod 13)).getD t.val 0

lemma f13_inj : Function.Injective f13 := by
  intro a b h
  revert a b
  decide +kernel

lemma f13_eq : ∀ t : ZMod 13, f13 (f13 t) = t + f13 (-t) := by decide +kernel

end DogmaCay

theorem solution : ∃ (D : Type) (star : D → D → D), Nat.card D = 13 ∧
    (∀ x y z : D, star x z = star y z → x = y) ∧ (∀ x y : D, star (star x y) y = star y x) ∧
    ∃ a b c d : D, star (star a b) (star c d) ≠ star (star a c) (star b d) := by
  refine ⟨ZMod 13, DogmaCay.cstar DogmaCay.f13, ?_, ?_, ?_, ?_⟩
  · simp [Nat.card_zmod]
  · exact DogmaCay.cstar_rc _ DogmaCay.f13_inj
  · exact DogmaCay.cstar_id _ DogmaCay.f13_eq
  · refine ⟨0, 0, 1, 2, ?_⟩
    decide +kernel

