-- Prove2me | solution 1 for Egrs75.Finish.repair_step_lex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:08.917153+00:00
-- url     : https://prove2.me/submissions/4b11502b-e90c-4357-91c9-4a0de7a98937

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
public import Theorems.Thm_Egrs75_Finish_badPrefix_drop_of_top_cleared
public import Theorems.Thm_Egrs75_Finish_egrs_clearing

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
    ∃ n', LowDigits p n' ∧ N < n' ∧ badPrefix q n' < badPrefix q n := by
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨n', hpn', hN', hcleared⟩ :=
    egrs_clearing hp hq hpo hqo hpq N hpn hNn hbad
  exact ⟨n', hpn', hN', badPrefix_drop_of_top_cleared hq1 hbad hcleared⟩
end Egrs75.Finish
