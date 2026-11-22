-- Prove2me | solution 1 for Egrs75.Finish.badPrefix_drop_of_top_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:41:15.574204+00:00
-- url     : https://prove2.me/submissions/c956899e-0d59-451f-9451-d964654fc4c0

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
public import Theorems.Thm_Egrs75_Finish_two_pow_top_le_badPrefix

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
theorem _root_.solution {q n n' : ℕ} (hq : 1 < q)
    (hbad : 0 < badCountQ q n)
    (hcleared : ∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') :
    badPrefix q n' < badPrefix q n := by
  set j := topBadIndex q n with hj
  -- upper bound on badPrefix q n'
  have hub : badPrefix q n' < 2 ^ j := by
    unfold badPrefix
    apply Nat.geomSum_lt (by omega)
    intro k hk
    -- k ∈ badIndexSet q n' ⟹ BadAt q k n' ⟹ k < j (else cleared)
    rw [mem_badIndexSet_iff hq] at hk
    by_contra hcon
    simp_all
  -- lower bound on badPrefix q n
  have hlb : 2 ^ j ≤ badPrefix q n := two_pow_top_le_badPrefix hq hbad
  omega
end Egrs75.Finish
