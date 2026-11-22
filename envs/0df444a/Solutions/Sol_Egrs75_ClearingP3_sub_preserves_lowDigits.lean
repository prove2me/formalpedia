-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_preserves_lowDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:19.361783+00:00
-- url     : https://prove2.me/submissions/aa8858be-1083-4caf-8a54-6ab4a5966ba1

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_digit_at_lowPDigitIndex_pos
public import Theorems.Thm_Egrs75_ClearingP3_sub_block_lowDigits
public import Theorems.Thm_Egrs75_ClearingP3_sub_block_lt
public import Theorems.Thm_Egrs75_ClearingP3_mod_pow_succ_lowPDigitIndex
public import Theorems.Thm_Egrs75_RepairDV_lowDigits_disjoint_add
public import Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_iff_digitAt


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP3
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hodd : Odd p) {n : ℕ}
    (hpn : LowDigits p n) (hn : n ≠ 0) :
    LowDigits p (n - (p ^ (lowPDigitIndex p n) + 1) / 2) := by
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hodd with ⟨k, hk⟩; omega
  have hp1 : 1 < p := by omega
  set m := lowPDigitIndex p n with hm
  set a := n / p ^ m % p with ha
  -- a is the lowest nonzero digit: 1 ≤ a ≤ (p-1)/2
  have ha1 : 1 ≤ a := digit_at_lowPDigitIndex_pos hp hn
  have haA : a ≤ (p - 1) / 2 := by
    rw [lowDigits_iff_digitAt (by omega)] at hpn
    have := hpn m
    unfold digitAt at this
    simp_all
  -- low block: n % p^(m+1) = a·p^m
  have hlow : n % p ^ (m + 1) = a * p ^ m := mod_pow_succ_lowPDigitIndex hp1 hn
  -- high block
  set Hi := n / p ^ (m + 1) with hHi
  have hdecomp : n = a * p ^ m + p ^ (m + 1) * Hi := by
    have : n = n % p ^ (m + 1) + p ^ (m + 1) * (n / p ^ (m + 1)) := (Nat.mod_add_div n _).symm
    rw [hlow] at this; exact this
  -- Hi is LowDigits p (high block of a LowDigits p number)
  have hHilow : LowDigits p Hi := by
    rw [lowDigits_iff_digitAt (by omega)] at hpn ⊢
    intro i
    unfold digitAt
    -- Hi / p^i % p = n / p^(m+1+i) % p, a digit of n
    have hdiv : Hi / p ^ i = n / p ^ (m + 1 + i) := by
      rw [hHi, Nat.div_div_eq_div_mul, ← pow_add]
    rw [hdiv]
    have := hpn (m + 1 + i)
    unfold digitAt at this
    exact this
  -- (p^m+1)/2 ≤ a·p^m  (a ≥ 1, p^m ≥ 1)
  have hSle : (p ^ m + 1) / 2 ≤ a * p ^ m := by
    have hpmpos : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
    have hS_lt : (p ^ m + 1) / 2 ≤ p ^ m := by
      have hoddpow : Odd (p ^ m) := hodd.pow
      obtain ⟨k, hk⟩ := hoddpow; rw [hk]; omega
    calc (p ^ m + 1) / 2 ≤ p ^ m := hS_lt
      _ = 1 * p ^ m := by ring
      _ ≤ a * p ^ m := Nat.mul_le_mul_right _ ha1
  -- n - S = (a·p^m - S) + p^(m+1)·Hi
  have hsubeq : n - (p ^ m + 1) / 2 = (a * p ^ m - (p ^ m + 1) / 2) + p ^ (m + 1) * Hi := by
    rw [hdecomp]
    omega
  rw [hsubeq]
  -- low block LowDigits p and < p^(m+1); assemble via disjoint adder
  have hblowlow : LowDigits p (a * p ^ m - (p ^ m + 1) / 2) := sub_block_lowDigits hp3 hodd ha1 haA
  have hblowlt : a * p ^ m - (p ^ m + 1) / 2 < p ^ (m + 1) := sub_block_lt hp3 hodd ha1 haA
  rcases Nat.eq_zero_or_pos Hi with hHi0 | hHipos
  · -- Hi = 0: n - S is just the low block
    rw [hHi0, Nat.mul_zero, Nat.add_zero]; exact hblowlow
  · exact lowDigits_disjoint_add hp1 hblowlt hHipos hblowlow hHilow
end Egrs75.ClearingP3
