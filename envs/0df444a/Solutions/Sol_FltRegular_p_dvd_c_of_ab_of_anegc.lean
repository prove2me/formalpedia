-- Prove2me | solution 1 for FltRegular.p_dvd_c_of_ab_of_anegc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:03.072081+00:00
-- url     : https://prove2.me/submissions/2cb1209e-7b60-48ba-9529-71f6b125cde7

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Definitions.Def_FltRegular_MayAssume_Lemmas

set_option autoImplicit false
@[expose] public section
public section
open Int Finset
open FltRegular
namespace FltRegular
theorem _root_.solution {p : ℕ} {a b c : ℤ} (hpri : p.Prime)
    (hp : p ≠ 3) (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p])
    (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by
  have : Fact p.Prime := ⟨hpri⟩
  replace h := congr_arg (fun n : ℤ => (n : ZMod p)) h
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at h
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_neg] at hbc hab
  rw [hab, hbc, ← sub_eq_zero, ← sub_eq_add_neg, ← Int.cast_neg, ← Int.cast_sub,
    ← Int.cast_sub] at h
  ring_nf at h
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, neg_eq_zero, mul_eq_zero] at h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine Or.resolve_right h fun h3 ↦ ?_
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_zero_iff,
    Nat.dvd_prime Nat.prime_three] at h3
  exact h3.elim hpri.ne_one hp
end FltRegular
