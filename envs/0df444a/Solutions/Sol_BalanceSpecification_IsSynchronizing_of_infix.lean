-- Prove2me | solution 1 for BalanceSpecification.IsSynchronizing.of_infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:23.715244+00:00
-- url     : https://prove2.me/submissions/72d6eff8-8349-4aaa-83d2-02b7cf4a150a

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Theorems.Thm_BalanceSpecification_IsFactorial_prefix
public import Theorems.Thm_BalanceSpecification_IsFactorial_suffix
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}
namespace BalanceSpecification
namespace IsSynchronizing
theorem _root_.solution (hL : IsFactorial L) {v w : Word A}
    (hv : IsSynchronizing L v) (hw : w ∈ L) (hvw : v <:+: w) :
    IsSynchronizing L w := by
  obtain ⟨p, q, rfl⟩ := hvw
  refine ⟨hw, ?_⟩
  intro u z hu hz
  have hu' : (u ++ p) ++ v ∈ L := by
    apply hL.prefix (v := q)
    simpa only [List.append_assoc] using hu
  have hz' : v ++ (q ++ z) ∈ L := by
    apply hL.suffix (u := p)
    simpa only [List.append_assoc] using hz
  simpa only [List.append_assoc] using hv.2 (u ++ p) (q ++ z) hu' hz'
end IsSynchronizing
end BalanceSpecification
