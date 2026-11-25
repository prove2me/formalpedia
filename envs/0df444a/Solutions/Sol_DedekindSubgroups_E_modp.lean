-- Prove2me | solution 1 for DedekindSubgroups.E_modp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:14:03.85019+00:00
-- url     : https://prove2.me/submissions/58f9478c-3553-48da-ab07-eb42e61515fb

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
public import Theorems.Thm_DedekindSubgroups_six_mul_sum_sq
public import Theorems.Thm_DedekindSubgroups_twelve_ne_zero
public import Theorems.Thm_DedekindSubgroups_two_h_E

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p) (hinv : h * h' % p = 1) :
    ∃ e : ℤ, E h p = p * e ∧ (((12 * e : ℤ)) : ZMod p) = (h : ZMod p) + (h' : ZMod p) := by
  have hp0 : 0 < p := hp.out.pos
  have h12 : (12 : ZMod p) ≠ 0 := twelve_ne_zero hp3
  have hhh : (h : ZMod p) * (h' : ZMod p) = 1 := by
    have : ((h * h' % p : ℕ) : ZMod p) = 1 := by rw [hinv, Nat.cast_one]
    rwa [ZMod.natCast_mod, Nat.cast_mul] at this
  have hkey : 12 * (h : ℤ) * E h p = ((h : ℤ) ^ 2 + 1) * ((p : ℤ) * (p - 1) * (2 * p - 1))
      - 6 * (p : ℤ) ^ 2 * ∑ r ∈ range p, ((h * r / p : ℕ) : ℤ) ^ 2 := by
    linear_combination 6 * two_h_E hp0 hinv + ((h : ℤ) ^ 2 + 1) * six_mul_sum_sq p
  -- `p ∣ E`
  have hE0 : ((E h p : ℤ) : ZMod p) = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hkey
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_one,
      Int.cast_natCast, Int.cast_ofNat, ZMod.natCast_self, zero_mul, mul_zero, zero_pow two_ne_zero,
      sub_zero, sub_self] at this
    have hh0 : (h : ZMod p) ≠ 0 := left_ne_zero_of_mul_eq_one hhh
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (mul_ne_zero h12 hh0)
    · exact h1
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hE0
  refine ⟨e, he, ?_⟩
  have hred : 12 * (h : ℤ) * e = ((h : ℤ) ^ 2 + 1) * ((p - 1) * (2 * p - 1))
      - 6 * p * ∑ r ∈ range p, ((h * r / p : ℕ) : ℤ) ^ 2 := by
    have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
    refine mul_left_cancel₀ hp0' ?_
    rw [he] at hkey
    linear_combination hkey
  have hredp := congrArg (fun z : ℤ => (z : ZMod p)) hred
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_one,
    Int.cast_natCast, Int.cast_ofNat, ZMod.natCast_self, zero_mul, mul_zero, sub_zero,
    zero_sub] at hredp
  push_cast
  linear_combination (h' : ZMod p) * hredp + ((h : ZMod p) - 12 * (e : ZMod p)) * hhh
end DedekindSubgroups
