-- Prove2me | solution 1 for BalanceSpecification.finitePointProbability_cylinder_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:10.666725+00:00
-- url     : https://prove2.me/submissions/bb6615f8-af3c-40be-b73e-d15157353d0c

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_finitePointProbability_real_apply
public import Theorems.Thm_BalanceSpecification_block_eq_drop_take
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_occurrenceFinset_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shiftMap_iterate_val
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
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
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution
    (u : Word A) (a b : ℕ)
    [Nonempty ↥(wordFinset (language X) (a + u.length + b))]
    (x : ↥(wordFinset (language X) (a + u.length + b)) → X.carrier)
    (hx : ∀ w, block (x w).val 0 (a + u.length + b) = w.val) :
    (finitePointProbability (fun w => (shiftMap X)^[a] (x w)) : Measure X.carrier).real
        (cylinder X u 0) =
      ((occurrenceFinset (language X) u a b).card : ℝ) /
        wordCount (language X) (a + u.length + b) := by
  classical
  rw [finitePointProbability_real_apply _ (measurableSet_cylinder X u 0)]
  have hmem (w : ↥(wordFinset (language X) (a + u.length + b))) :
      (shiftMap X)^[a] (x w) ∈ cylinder X u 0 ↔
        w.val ∈ occurrenceFinset (language X) u a b := by
    change block ((shiftMap X)^[a] (x w)).val 0 u.length = u ↔ _
    rw [shiftMap_iterate_val, block_shift, add_zero,
      block_eq_drop_take _ (show a + u.length ≤ a + u.length + b by omega), hx]
    rw [mem_occurrenceFinset_iff (language_factorial X)]
    exact ⟨fun h => ⟨(mem_wordFinset.mp w.property).1,
      (mem_wordFinset.mp w.property).2, h⟩, fun h => h.2.2⟩
  have hcard :
      (Finset.univ.filter fun w => (shiftMap X)^[a] (x w) ∈ cylinder X u 0).card =
        (occurrenceFinset (language X) u a b).card := by
    apply Finset.card_bij (fun w _ => w.val)
    · intro w hw
      exact (hmem w).mp (Finset.mem_filter.mp hw).2
    · intro w hw z hz heq
      exact Subtype.ext heq
    · intro w hw
      obtain ⟨hwL, hwlen, _⟩ := (mem_occurrenceFinset_iff (language_factorial X)).mp hw
      let z : ↥(wordFinset (language X) (a + u.length + b)) :=
        ⟨w, mem_wordFinset.mpr ⟨hwL, hwlen⟩⟩
      exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem z).mpr hw⟩, rfl⟩
  rw [hcard]
  simp only [Fintype.card_coe, wordCount]
end BalanceSpecification
