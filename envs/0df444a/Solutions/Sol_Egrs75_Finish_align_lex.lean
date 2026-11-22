-- Prove2me | solution 1 for Egrs75.Finish.align_lex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:09.60697+00:00
-- url     : https://prove2.me/submissions/88897829-e045-4417-8ab5-8c479f2d6ce6

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
public import Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe
namespace Egrs75.Finish
theorem _root_.solution {p q : ℕ} (N : ℕ)
    (hrepair_lex : ∀ {n : ℕ}, LowDigits p n → N < n → 0 < badCountQ q n →
      ∃ n', LowDigits p n' ∧ N < n' ∧ badPrefix q n' < badPrefix q n)
    (seed : ℕ) (hseedN : N < seed) (hseedp : LowDigits p seed) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  -- Strong induction on the base-`q` bitmask of the running number, carrying the
  -- invariants `N < n` and `LowDigits p n`.
  suffices H : ∀ k, ∀ n, badPrefix q n = k → N < n → LowDigits p n →
      ∃ m, N < m ∧ LowDigits p m ∧ LowDigits q m by
    exact H (badPrefix q seed) seed rfl hseedN hseedp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hN hpn
    rcases Nat.eq_zero_or_pos (badCountQ q n) with hzero | hpos
    · -- bad count 0 ⟹ already LowDigits q : done with `n` itself
      exact ⟨n, hN, hpn, (badCountQ_eq_zero_iff_lowDigits).mp hzero⟩
    · -- bad count > 0 ⟹ repair once (threading the magnitude `N < n`), recurse on the
      -- strictly smaller bitmask
      obtain ⟨n', hpn', hN', hdrop⟩ := hrepair_lex hpn hN hpos
      have hk' : badPrefix q n' < k := by rw [← hk]; exact hdrop
      exact ih (badPrefix q n') hk' n' rfl hN' hpn'
end Egrs75.Finish
