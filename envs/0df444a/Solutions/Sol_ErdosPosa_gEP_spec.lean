-- Prove2me | solution 1 for ErdosPosa.gEP_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:09.835965+00:00
-- url     : https://prove2.me/submissions/df9275dd-9031-431e-825e-1c5f558858c9

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPin
public import Definitions.Def_ErdosPosaLib_EPMain

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution (k : ℕ) :
    (gEP k : ℤ) + 2 * (2 * Nat.log 2 (gEP (k + 1) + 1) + 3) ≤ gEP (k + 1) := by
  set L := Nat.log 2 (k + 1) with hL
  have hL0 : Nat.log 2 k ≤ L := Nat.log_mono_right (Nat.le_succ k)
  have h1 : k + 1 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) (k + 1)
  have h2 : L + 1 < 2 ^ (L + 1) := Nat.lt_two_pow_self
  have hP : 2 ^ (2 * L + 8) = 64 * (2 ^ (L + 1) * 2 ^ (L + 1)) := by
    rw [← pow_add]; rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; ring
  have h3 : gEP (k + 1) + 1 < 2 ^ (2 * L + 8) := by
    rw [hP]
    unfold gEP
    rw [← hL]
    have : (k + 1) * (L + 1) < 2 ^ (L + 1) * 2 ^ (L + 1) :=
      Nat.mul_lt_mul'' h1 h2
    nlinarith
  have h4 : Nat.log 2 (gEP (k + 1) + 1) < 2 * L + 8 :=
    Nat.log_lt_of_lt_pow (by omega) h3
  have h5 : gEP k ≤ 64 * k * (L + 1) := by
    unfold gEP
    exact Nat.mul_le_mul_left _ (by omega)
  have h6 : gEP (k + 1) = 64 * k * (L + 1) + 64 * (L + 1) := by
    unfold gEP; rw [← hL]; ring
  omega
end ErdosPosa
