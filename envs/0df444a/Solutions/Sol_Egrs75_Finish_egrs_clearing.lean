-- Prove2me | solution 1 for Egrs75.Finish.egrs_clearing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:25.313439+00:00
-- url     : https://prove2.me/submissions/c4a5d005-d709-447c-9eba-d707ba65992d

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
public import Theorems.Thm_Egrs75_Finish_egrs_clearing_low
public import Theorems.Thm_Egrs75_Probe_clearing_high


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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by
  -- Odd primes are ≥ 3.
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hpo with ⟨k, hk⟩; omega
  have hq3 : 3 ≤ q := by have h2 := hq.two_le; rcases hqo with ⟨k, hk⟩; omega
  rcases lt_or_ge N (q ^ (topBadIndex q n)) with hhigh | hlow
  · -- `N < q^j`: free window number, no carry control needed (KERNEL-CLEAN).
    exact clearing_high hp3 hpo hq3 N hhigh
  · -- `q^j ≤ N`: the genuine EGRS carry-control residual.
    exact egrs_clearing_low hp hq hpo hqo hpq N hpn hNn hbad hlow
end Egrs75.Finish
