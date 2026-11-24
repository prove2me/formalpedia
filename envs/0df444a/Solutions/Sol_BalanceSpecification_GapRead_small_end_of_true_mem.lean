-- Prove2me | solution 1 for BalanceSpecification.GapRead.small_end_of_true_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:13.350584+00:00
-- url     : https://prove2.me/submissions/14d25c6a-fa7b-456b-bf13-2010199b1a94

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false_iff
public import Theorems.Thm_BalanceSpecification_eq_replicate_false_of_true_not_mem

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open BalanceSpecification.GapRead
variable {S : Set ℕ} {N a b : ℕ} {w : Word Bool}
namespace BalanceSpecification.GapRead
theorem _root_.solution
    (hN : ∀ t, GapState S t → ∃ s ∈ S, t ≤ s ∧ s ≤ t + N)
    (h : GapRead S a w b) (ht : true ∈ w) :
    ∃ b', b' ≤ N ∧ GapRead S a w b' := by
  induction h with
  | nil => exact False.elim (List.not_mem_nil ht)
  | zero h ih =>
    obtain hfalse | ht' := List.mem_cons.mp ht
    · cases hfalse
    · obtain ⟨b', hb', hread⟩ := ih ht'
      exact ⟨b', hb', .zero hread⟩
  | @one s j v hs h ih =>
    by_cases htrue : true ∈ v
    · obtain ⟨b', hb', hread⟩ := ih htrue
      exact ⟨b', hb', .one hs hread⟩
    · have hv := eq_replicate_false_of_true_not_mem htrue
      have hreadzeros : GapRead S s (List.replicate v.length false) j := hv ▸ h
      have hslen : s = j + v.length := replicate_false_iff.mp hreadzeros
      obtain ⟨r, hr, hl, hu⟩ := hN v.length ⟨s, hs, by omega⟩
      refine ⟨r - v.length, by omega, GapRead.one hr ?_⟩
      have hnew : GapRead S r (List.replicate v.length false) (r - v.length) := by
        convert replicate_false (S := S) (r - v.length) v.length using 1; omega
      exact (congrArg (fun t : Word Bool => GapRead S r t (r - v.length)) hv).mpr hnew
end BalanceSpecification.GapRead
