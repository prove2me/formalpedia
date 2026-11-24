-- Prove2me | solution 1 for BalanceSpecification.cylinder_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:10.643915+00:00
-- url     : https://prove2.me/submissions/749f8617-958b-4354-8b9a-2d9ff5a4466c

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_block_append
public import Theorems.Thm_BalanceSpecification_block_subword
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) (v w : Word A) (k : ℤ) :
    cylinder X (v ++ w) k = cylinder X v k ∩ cylinder X w (k + v.length) := by
  ext x
  constructor
  · intro h
    change block x.val k (v ++ w).length = v ++ w at h
    constructor
    · have H := block_subword x.val k [] v w
        (by simpa only [List.nil_append] using h)
      change block x.val k v.length = v
      simpa only [List.length_nil, Nat.cast_zero, add_zero] using H
    · exact block_subword x.val k v w []
        (by simpa only [List.append_nil] using h)
  · rintro ⟨hv, hw⟩
    change block x.val k (v ++ w).length = v ++ w
    change block x.val k v.length = v at hv
    change block x.val (k + v.length) w.length = w at hw
    rw [List.length_append, block_append, hv, hw]
end BalanceSpecification
