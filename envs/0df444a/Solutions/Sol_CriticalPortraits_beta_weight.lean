-- Prove2me | solution 1 for CriticalPortraits.beta_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:35:38.547321+00:00
-- url     : https://prove2.me/submissions/6201b420-f869-4be0-b03d-2336c0d1abd9

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Theorems.Thm_CriticalPortraits_mem_beta_iff
public import Theorems.Thm_CriticalPortraits_T_beta
public import Theorems.Thm_CriticalPortraits_beta_pairwise_disjoint

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcard : U.card = d - 1) (hcanon : LevelCanonical d m U) :
    ∑ S ∈ beta U, (S.card - 1) = d - 1 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  -- pairwise disjoint eraseMin
  have hpd : (↑(beta U) : Set (Finset (ZMod (d*m)))).PairwiseDisjoint eraseMin := by
    intro A hA B hB hAB
    exact (beta_pairwise_disjoint A hA B hB hAB).mono (eraseMin_subset A) (eraseMin_subset B)
  have hTcard : (T (beta U)).card = ∑ S ∈ beta U, (S.card - 1) := by
    unfold T
    rw [Finset.sup_eq_biUnion, Finset.card_biUnion hpd]
    apply Finset.sum_congr rfl
    intro S hS
    rw [mem_beta_iff] at hS
    obtain ⟨v, hv, hSeq⟩ := hS
    subst hSeq
    exact eraseMin_card (betaBlock U v) (betaBlock_nonempty hv)
  rw [← hTcard, T_beta hd hm hcanon, hcard]
end CriticalPortraits
