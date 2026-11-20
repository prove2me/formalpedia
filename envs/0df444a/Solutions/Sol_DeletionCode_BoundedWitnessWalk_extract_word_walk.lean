-- Prove2me | solution 1 for DeletionCode.BoundedWitnessWalk.extract_word_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:03:02.019055+00:00
-- url     : https://prove2.me/submissions/6c8a5676-7bd2-4a5a-a749-6b77bba747b9

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Theorems.Thm_DeletionCode_BoundedWitnessWalk_extract_counted
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SpectrumPath_kunique_mono
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_boolean
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases
namespace DeletionCode.BoundedWitnessWalk
theorem _root_.solution {t k m n : ℕ} (ht : 2 ≤ t)
    (words : Fin (m + 1) → Letters)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ j, Windows.KUnique (words j) n k)
    (hclosed : Agree (words 0) 0 (words (Fin.last m)) 0 n) (hodd : Odd m)
    (hcat : ∀ i : Fin m, CatalogueRule t k
      (wordSpectrum (words i.succ) n (windowLength k) -
       wordSpectrum (words i.castSucc) n (windowLength k)))
    (hK : ∀ i : Fin m, (wordSpectrum (words i.succ) n (windowLength k) -
       wordSpectrum (words i.castSucc) n (windowLength k)) ∈ K) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (words 0) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (words 0) n k U.card (componentCount U) U := by
  classical
  let p := fun j => wordSpectrum (words j) n (windowLength k)
  have hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j) := by
    intro j g
    have hku := SpectrumPath.kunique_mono (words j) n k (windowLength k - 1)
      (hunique j) (by unfold windowLength; omega)
    rcases SpectrumPath.spectrum_boolean (words j) n (windowLength k) hku g with hz | ho
    · left; change (wordSpectrum (words j) n (windowLength k) g : ℚ) = 0
      exact_mod_cast hz
    · right; change (wordSpectrum (words j) n (windowLength k) g : ℚ) = 1
      exact_mod_cast ho
  have hclosedP : p 0 = p (Fin.last m) := by
    funext g
    unfold p wordSpectrum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val + windowLength k ≤ n
    · have heq : gram (words 0) (windowLength k) i.val =
          gram (words (Fin.last m)) (windowLength k) i.val := by
        funext q
        have hq := hclosed (i.val + q.val) (by have := q.isLt; omega)
        simpa only [Nat.zero_add, gram] using hq
      simp only [hi, true_and, heq]
    · simp only [hi, false_and, ite_false]
  exact extract_counted ht (words 0) p K rfl hp hclosedP hodd hcat hK
end DeletionCode.BoundedWitnessWalk
