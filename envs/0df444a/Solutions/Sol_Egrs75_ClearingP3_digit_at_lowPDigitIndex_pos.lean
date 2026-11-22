-- Prove2me | solution 1 for Egrs75.ClearingP3.digit_at_lowPDigitIndex_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:00.639171+00:00
-- url     : https://prove2.me/submissions/dd896d21-3a7f-4df2-afa1-1cf53025f77c

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_pow_lowPDigitIndex_dvd
public import Theorems.Thm_Egrs75_ClearingP3_not_pow_succ_lowPDigitIndex_dvd

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
theorem _root_.solution {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    0 < n / p ^ (lowPDigitIndex p n) % p := by
  set m := lowPDigitIndex p n with hm
  have hp1 : 1 < p := hp.one_lt
  have hdvd : p ^ m ∣ n := pow_lowPDigitIndex_dvd hp1 hn
  have hnot : ¬ p ^ (m + 1) ∣ n := not_pow_succ_lowPDigitIndex_dvd hp hn
  -- if the digit were 0, then p^(m+1) ∣ n
  by_contra hcon
  push Not at hcon
  have hzero : n / p ^ m % p = 0 := Nat.le_zero.mp hcon
  apply hnot
  -- n = p^m * (n / p^m); and p ∣ (n / p^m) since (n/p^m)%p = 0
  obtain ⟨c, hc⟩ := hdvd
  have hdivc : n / p ^ m = c := by
    rw [hc, Nat.mul_div_cancel_left _ (pow_pos (by omega) m)]
  rw [hdivc] at hzero
  have hpc : p ∣ c := Nat.dvd_of_mod_eq_zero hzero
  obtain ⟨d, hd⟩ := hpc
  rw [hc, hd, pow_succ]
  exact ⟨d, by ring⟩
end Egrs75.ClearingP3
