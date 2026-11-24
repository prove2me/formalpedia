-- Prove2me | solution 1 for BalanceSpecification.mem_subshiftCylinderEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:53.656478+00:00
-- url     : https://prove2.me/submissions/0cdc68c6-711b-4a56-8df2-dd922c845dd0

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_avoidingLanguage
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_languageShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {X Y : ShiftSpace A} {n : ℕ} {x : X.carrier} :
    x ∈ subshiftCylinderEvent X Y n ↔
      block x.val (-(n : ℤ)) (2 * n + 1) ∈ language Y := by
  constructor
  · intro h
    obtain ⟨w, h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hw, hx⟩ := Set.mem_iUnion.mp h
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    have he : block x.val (-(n : ℤ)) (2 * n + 1) = w := by
      simpa only [cylinder, Set.mem_ofPred_eq, hwlen] using hx
    exact he ▸ hwL
  · intro h
    apply Set.mem_iUnion.mpr
    refine ⟨block x.val (-(n : ℤ)) (2 * n + 1), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact mem_wordFinset.mpr ⟨h, length_block _ _ _⟩
    · change block x.val (-(n : ℤ)) (block x.val (-(n : ℤ)) (2 * n + 1)).length = _
      rw [length_block]
end BalanceSpecification
