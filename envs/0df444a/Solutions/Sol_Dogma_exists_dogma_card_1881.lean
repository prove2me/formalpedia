-- Prove2me | solution 1 for Dogma.exists_dogma_card_1881
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:29:50.04666+00:00
-- url     : https://prove2.me/submissions/2cc42f7a-7aa7-4fc8-b350-a1d3e8a0b4ee

import Mathlib

set_option autoImplicit false

namespace DogmaSol

/-- Component on `ZMod 11`: `x ⋆ y = 3x + 9y`, where `3² + 3 = 12 = 1`. -/
def op11 (x y : ZMod 11) : ZMod 11 := 3 * x + 9 * y
/-- Component on `ZMod 19`: `x ⋆ y = 4x + 16y`, where `4² + 4 = 20 = 1`. -/
def op19 (x y : ZMod 19) : ZMod 19 := 4 * x + 16 * y
/-- Component on `F₉ = F₃[φ]/(φ² + φ - 1)`, elements `a + bφ` written `(a, b)`:
`x ⋆ y = φ x + φ² y` with `φ x = (b, a - b)` and `φ² y = (c - d, 2d - c)`. -/
def opF9 (x y : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.2 + (y.1 - y.2), x.1 - x.2 + (2 * y.2 - y.1))

lemma rc11 : ∀ x y z : ZMod 11, op11 x z = op11 y z → x = y := by decide
lemma id11 : ∀ x y : ZMod 11, op11 (op11 x y) y = op11 y x := by decide
lemma rc19 : ∀ x y z : ZMod 19, op19 x z = op19 y z → x = y := by decide
lemma id19 : ∀ x y : ZMod 19, op19 (op19 x y) y = op19 y x := by decide
lemma rcF9 : ∀ x y z : ZMod 3 × ZMod 3, opF9 x z = opF9 y z → x = y := by decide
lemma idF9 : ∀ x y : ZMod 3 × ZMod 3, opF9 (opF9 x y) y = opF9 y x := by decide

abbrev D : Type := ZMod 11 × ZMod 19 × (ZMod 3 × ZMod 3)

def star (x y : D) : D := (op11 x.1 y.1, op19 x.2.1 y.2.1, opF9 x.2.2 y.2.2)

end DogmaSol

theorem solution : ∃ (D : Type) (star : D → D → D), Nat.card D = 1881 ∧
    (∀ x y z : D, star x z = star y z → x = y) ∧ ∀ x y : D, star (star x y) y = star y x := by
  refine ⟨DogmaSol.D, DogmaSol.star, ?_, ?_, ?_⟩
  · simp [DogmaSol.D, Nat.card_prod, Nat.card_zmod]
  · intro x y z h
    obtain ⟨x1, x2, x3⟩ := x
    obtain ⟨y1, y2, y3⟩ := y
    obtain ⟨z1, z2, z3⟩ := z
    simp only [DogmaSol.star, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [DogmaSol.rc11 x1 y1 z1 h1, DogmaSol.rc19 x2 y2 z2 h2, DogmaSol.rcF9 x3 y3 z3 h3]
  · intro x y
    obtain ⟨x1, x2, x3⟩ := x
    obtain ⟨y1, y2, y3⟩ := y
    simp only [DogmaSol.star, Prod.mk.injEq]
    exact ⟨DogmaSol.id11 x1 y1, DogmaSol.id19 x2 y2, DogmaSol.idF9 x3 y3⟩

