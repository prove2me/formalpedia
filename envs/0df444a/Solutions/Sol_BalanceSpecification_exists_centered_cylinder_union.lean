-- Prove2me | solution 1 for BalanceSpecification.exists_centered_cylinder_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:55:13.162414+00:00
-- url     : https://prove2.me/submissions/7357366f-6d4a-4743-a810-5a2bddf490c9

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Theorems.Thm_BalanceSpecification_cylinder_nil
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
attribute [local simp] BalanceSpecification.cylinder_nil
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
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution [Fintype A] {X : ShiftSpace A}
    {E : Set X.carrier} (hE : E ∈ finiteCylinderAlgebra X) :
    ∃ n : ℕ, ∃ S : Finset (Word A),
      (∀ w ∈ S, w ∈ language X ∧ w.length = 2 * n + 1) ∧
      E = ⋃ w ∈ S, cylinder X w (-(n : ℤ)) := by
  classical
  obtain ⟨n, hn⟩ := hE
  let S := (allWords (A := A) (2 * n + 1)).filter
    (fun w => ∃ x : X.carrier, x ∈ E ∧ block x.val (-(n : ℤ)) (2 * n + 1) = w)
  refine ⟨n, S, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwlen, x, _, hxblock⟩ := Finset.mem_filter.mp hw
    have hlen := mem_allWords.mp hwlen
    exact ⟨⟨x.val, x.property, -(n : ℤ), by simpa only [hlen] using hxblock⟩, hlen⟩
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      let w := block x.val (-(n : ℤ)) (2 * n + 1)
      have hw : w ∈ S := Finset.mem_filter.mpr
        ⟨mem_allWords.mpr (length_block _ _ _), x, hx, rfl⟩
      refine ⟨w, hw, ?_⟩
      change block x.val (-(n : ℤ)) w.length = w
      simp only [w, length_block]
    · rintro ⟨w, hw, hx⟩
      obtain ⟨hwlen, y, hy, hyblock⟩ := Finset.mem_filter.mp hw
      have hwlength : w.length = 2 * n + 1 := mem_allWords.mp hwlen
      have hxblock : block x.val (-(n : ℤ)) (2 * n + 1) = w := by
        simpa only [cylinder, Set.mem_ofPred_eq, hwlength] using hx
      exact (hn x y (hxblock.trans hyblock.symm)).mpr hy
end BalanceSpecification
