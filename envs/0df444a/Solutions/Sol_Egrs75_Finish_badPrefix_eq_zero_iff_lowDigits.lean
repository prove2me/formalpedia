-- Prove2me | solution 1 for Egrs75.Finish.badPrefix_eq_zero_iff_lowDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:11.30398+00:00
-- url     : https://prove2.me/submissions/b14b1945-64c7-4688-8bae-1d267472c2a4

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
public import Theorems.Thm_Egrs75_Finish_mem_badIndexSet_iff
public import Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits
public import Theorems.Thm_Egrs75_RepairDV_badIndexSet_nonempty
public import Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_iff_digitAt


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
theorem _root_.solution {q n : ℕ} (hq : 1 < q) :
    badPrefix q n = 0 ↔ LowDigits q n := by
  rw [← badCountQ_eq_zero_iff_lowDigits]
  unfold badPrefix
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    -- every term is 0, but 2^i > 0, so the set is empty ⟹ badCountQ = 0
    by_contra hne
    have hpos : 0 < badCountQ q n := Nat.pos_of_ne_zero hne
    obtain ⟨i, hi⟩ := badIndexSet_nonempty hq hpos
    simp_all
  · intro h0 i hi
    -- badCountQ = 0 ⟹ badIndexSet empty ⟹ no such i
    rw [badCountQ_eq_zero_iff_lowDigits] at h0
    rw [mem_badIndexSet_iff hq] at hi
    -- LowDigits q n contradicts BadAt q i n
    rw [lowDigits_iff_digitAt (by omega)] at h0
    unfold BadAt at hi
    have := h0 i
    omega
end Egrs75.Finish
