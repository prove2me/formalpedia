-- Prove2me | solution 1 for BitDFT.bval_foldField_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T04:37:46.5005+00:00
-- url     : https://prove2.me/submissions/491a9398-bbfc-4dff-bfa2-39969882499d

import Mathlib
import Definitions.Def_BitDFT_bval
import Definitions.Def_BitDFT_foldField

set_option autoImplicit false
noncomputable section
open BitDFT

namespace FoldPrelude

theorem foldField_fst_false (κ : Bool) (l : List Bool) :
    (foldField false κ l).1 = (addBits κ l).1 := by
  induction l generalizing κ with
  | nil => rfl
  | cons b t ih =>
    have h1 : (false && !b) = false := rfl
    have h2 : ((b != false) && κ) = (b && κ) := by cases b <;> rfl
    have h3 : ((b != false) != κ) = (b != κ) := by cases b <;> rfl
    simp only [foldField, foldStep, h1, h2, h3, addBits]
    rw [ih]

theorem foldField_carry_false (κ : Bool) (l : List Bool) :
    (foldField false κ l).2.2.1 = (addBits κ l).2 := by
  induction l generalizing κ with
  | nil => rfl
  | cons b t ih =>
    have h1 : (false && !b) = false := rfl
    have h2 : ((b != false) && κ) = (b && κ) := by cases b <;> rfl
    have h3 : ((b != false) != κ) = (b != κ) := by cases b <;> rfl
    simp only [foldField, foldStep, h1, h2, h3, addBits]
    rw [ih]

theorem bval_addBits (κ : Bool) (l : List Bool) :
    bval (addBits κ l).1 + (addBits κ l).2.toNat * 2 ^ l.length = bval l + κ.toNat := by
  induction l generalizing κ with
  | nil => cases κ <;> simp [addBits, bval]
  | cons b t ih =>
    simp only [addBits, bval_cons, List.length_cons, Nat.pow_succ]
    have h := ih (b && κ)
    have hx : (b != κ).toNat + 2 * (b && κ).toNat = b.toNat + κ.toNat := by
      cases b <;> cases κ <;> simp
    cases hc : (addBits (b && κ) t).2 <;>
      simp only [hc, Bool.toNat_true, Bool.toNat_false, Nat.one_mul, Nat.zero_mul,
        Nat.add_zero] at h ⊢ <;> omega

end FoldPrelude

theorem solution (κ : Bool) (l : List Bool) :
    bval (foldField false κ l).1
        + (foldField false κ l).2.2.1.toNat * 2 ^ l.length = bval l + κ.toNat := by
  rw [FoldPrelude.foldField_fst_false, FoldPrelude.foldField_carry_false]
  exact FoldPrelude.bval_addBits κ l
