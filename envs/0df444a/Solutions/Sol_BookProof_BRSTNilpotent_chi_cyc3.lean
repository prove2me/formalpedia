-- Prove2me | solution 1 for BookProof.BRSTNilpotent.chi_cyc3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:54.339595+00:00
-- url     : https://prove2.me/submissions/4cef3ed2-b062-473c-ac39-21b0c5624b38

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.chi_cyc3
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem solution (χ β : Fin n → R) (hCAR : GhostCAR χ β) (a b c : Fin n) :
    χ a * χ b * χ c = χ b * χ c * χ a := by
  have h : ∀ x y : Fin n, χ x * χ y = -(χ y * χ x) := fun x y =>
    eq_neg_of_add_eq_zero_left (hCAR.chichi x y)
  rw [h a b, neg_mul, mul_assoc, h a c, mul_neg, neg_neg, ← mul_assoc]
