-- Prove2me | solution 1 for DeletionCode.WitnessCounting.candidate_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:34:24.023327+00:00
-- url     : https://prove2.me/submissions/8a988c7b-3d4e-4f73-8af4-3c5dd9af1aca

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting
import Theorems.Thm_DeletionCode_WitnessCounting_componentIndex_card_le
import Theorems.Thm_DeletionCode_WitnessCounting_partition_injective
import Theorems.Thm_DeletionCode_WitnessCounting_component_power_le
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_CountingLemma_generatingSet_finite
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_ManuscriptCounting_card_bound
import Theorems.Thm_DeletionCode_ManuscriptCounting_generatingSet_finite
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators
namespace DeletionCode.WitnessCounting
theorem _root_.solution (t : ℕ) (ht : 2 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 2 ≤ R) (hx : KUnique x n k) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R) :
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤
      2 ^ R * (2 * t * R + 1) * n ^ ((2 * t - 1) * R) *
        (windowLength k * R) ^ (exponent t * R) := by
  classical
  have ht' : 1 ≤ t := by omega
  have hR' : 1 ≤ R := by omega
  let : ∀ c : ComponentIndex t k R,
      Finite {U : RuleSet k // GeneratingSet t x n k R c.val.val U} :=
    fun c => generatingSet_finite t ht' x n k R c.val.val hR' hx
  let : Finite (IndexedSets t x n k R) := by unfold IndexedSets; infer_instance
  calc
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤ Nat.card (IndexedSets t x n k R) :=
      Nat.card_le_card_of_injective (partition t ht' x n k R hR')
        (partition_injective t ht' x n k R hR')
    _ = ∑ c : ComponentIndex t k R,
        Nat.card {U : RuleSet k // GeneratingSet t x n k R c.val.val U} := Nat.card_sigma
    _ ≤ ∑ _c : ComponentIndex t k R,
        2 ^ R * n ^ ((2 * t - 1) * R) *
          (windowLength k * R) ^ (exponent t * R) := by
      apply Finset.sum_le_sum
      intro c _hc
      exact (ManuscriptCounting.card_bound t ht' x n k R c.val.val hR' hx).trans
        (Nat.mul_le_mul_right _ (component_power_le t n k R c.val.val hn hbonus c.property))
    _ = Fintype.card (ComponentIndex t k R) *
        (2 ^ R * n ^ ((2 * t - 1) * R) *
          (windowLength k * R) ^ (exponent t * R)) := by simp
    _ ≤ (2 * t * R + 1) *
        (2 ^ R * n ^ ((2 * t - 1) * R) *
          (windowLength k * R) ^ (exponent t * R)) :=
      Nat.mul_le_mul_right _ (componentIndex_card_le t k R)
    _ = _ := by ring
end DeletionCode.WitnessCounting
