-- Prove2me | solution 1 for Dogma.exists_dogma_card_21
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:53:07.932012+00:00
-- url     : https://prove2.me/submissions/c3008393-f30f-4369-a0b6-74fd99eb90c2

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

def f21 (t : ZMod 21) : ZMod 21 :=
  ([0, 6, 16, 9, 11, 17, 8, 5, 18, 4, 19, 3, 2, 14, 10, 12, 15, 20, 1, 13, 7] : List (ZMod 21)).getD t.val 0

lemma f21_inj : Function.Injective f21 := by
  intro a b h
  revert a b
  decide +kernel

lemma f21_eq : ∀ t : ZMod 21, f21 (f21 t) = t + f21 (-t) := by decide +kernel

end DogmaCay

theorem solution : ∃ (D : Type) (star : D → D → D), Nat.card D = 21 ∧
    (∀ x y z : D, star x z = star y z → x = y) ∧ ∀ x y : D, star (star x y) y = star y x := by
  refine ⟨ZMod 21, DogmaCay.cstar DogmaCay.f21, ?_, ?_, ?_⟩
  · simp
  · exact DogmaCay.cstar_rc _ DogmaCay.f21_inj
  · exact DogmaCay.cstar_id _ DogmaCay.f21_eq

