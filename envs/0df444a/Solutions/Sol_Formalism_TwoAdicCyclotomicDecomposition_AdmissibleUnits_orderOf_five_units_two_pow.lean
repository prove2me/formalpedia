-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.orderOf_five_units_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:06.805804+00:00
-- url     : https://prove2.me/submissions/fe7f8599-1a6c-4342-ab79-6387dd8285e3

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace AdmissibleUnits
private lemma exists_one_add_two_pow_odd_pow_two_pow_eq (i m0 : ℕ) : ∀ k : ℕ, ∃ m : ℕ,
    (1 + 2 ^ (i + 2) * (2 * m0 + 1)) ^ (2 ^ k) = 1 + 2 ^ (k + (i + 2)) * (2 * m + 1) := by
  intro k
  induction k with
  | zero => exact ⟨m0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 2 ^ (i + k) * (2 * m + 1) ^ 2, ?_⟩
    rw [pow_succ 2 k, pow_mul, hm]
    ring
private lemma natCast_one_add_two_pow_mul_eq_one (N q : ℕ) : ((1 + 2 ^ N * q : ℕ) : ZMod (2 ^ N)) = 1 := by
  have h : ((2 ^ N : ℕ) : ZMod (2 ^ N)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_add, Nat.cast_mul, h, zero_mul, add_zero, Nat.cast_one]
private lemma natCast_one_add_two_pow_odd_ne_one (N m : ℕ) :
    ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) ≠ 1 := by
  intro h
  have h' : ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) = ((1 : ℕ) : ZMod (2 ^ (N + 1))) := by
    rw [h, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).1 h'.symm
  rw [Nat.add_sub_cancel_left, pow_succ] at h2
  have h3 := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos N) h2
  omega
private lemma unitOfCoprime_pow_eq_one_iff (N a e : ℕ) (h : Nat.Coprime a (2 ^ N)) :
    (ZMod.unitOfCoprime a h) ^ e = 1 ↔ ((a ^ e : ℕ) : ZMod (2 ^ N)) = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Nat.cast_pow]
end AdmissibleUnits
end Formalism.TwoAdicCyclotomicDecomposition
end

set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
theorem _root_.solution (n : ℕ) : orderOf (u5 (n + 2)) = 2 ^ n := by
  unfold u5
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff]
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  | succ n =>
    apply orderOf_eq_prime_pow
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 n
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_odd_ne_one _ _
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 (n + 1)
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_mul_eq_one _ _
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
