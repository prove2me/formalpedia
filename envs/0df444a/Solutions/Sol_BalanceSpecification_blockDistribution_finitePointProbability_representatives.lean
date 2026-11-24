-- Prove2me | solution 1 for BalanceSpecification.blockDistribution_finitePointProbability_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:55.269371+00:00
-- url     : https://prove2.me/submissions/a6f4e60d-ec07-4d32-9722-82162e9a5f0c

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_finitePointProbability_real_apply
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
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
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (N : ℕ)
    [Nonempty ↥(wordFinset (language X) N)]
    (x : ↥(wordFinset (language X) N) → X.carrier)
    (hx : ∀ w, block (x w).val 0 N = w.val)
    (w : ↥(wordFinset (language X) N)) :
    blockDistribution (finitePointProbability x) N w = 1 / wordCount (language X) N := by
  classical
  have hmem (v : ↥(wordFinset (language X) N)) :
      x v ∈ cylinder X w.val 0 ↔ v = w := by
    change block (x v).val 0 w.val.length = w.val ↔ v = w
    rw [(mem_wordFinset.mp w.property).2, hx v]
    exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  change (finitePointProbability x : Measure X.carrier).real (cylinder X w.val 0) = _
  rw [finitePointProbability_real_apply x (measurableSet_cylinder X w.val 0)]
  have hf : (Finset.univ.filter fun v => x v ∈ cylinder X w.val 0) = {w} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem, Finset.mem_singleton]
  rw [hf, Finset.card_singleton, Fintype.card_coe]
  simp only [Nat.cast_one, wordCount]
end BalanceSpecification
