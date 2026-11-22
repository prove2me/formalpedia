-- Prove2me | solution 1 for Egrs75.Finish.align_to_crux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:14.771+00:00
-- url     : https://prove2.me/submissions/b91dc719-7e7d-429c-80e6-c61df4c6974d

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
theorem _root_.solution {p q : ℕ}
    (halign : ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hN, hpn, hqn⟩ := halign N
  exact ⟨n, ⟨hpn, hqn⟩, hN⟩
end Egrs75.Finish
