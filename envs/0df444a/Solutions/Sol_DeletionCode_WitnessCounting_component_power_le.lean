-- Prove2me | solution 1 for DeletionCode.WitnessCounting.component_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:30:43.952583+00:00
-- url     : https://prove2.me/submissions/3e4667ca-042c-4f31-a187-70c15131d11b

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
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
theorem _root_.solution (t n k R c : ℕ) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R)
    (hc : AllowedComponents t k R c) :
    n ^ c ≤ 2 ^ R * n ^ ((2 * t - 1) * R) := by
  by_cases hsmall : R ≤ windowLength k
  · calc
      n ^ c ≤ n ^ ((2 * t - 1) * R) := Nat.pow_le_pow_right (by omega) (hc.2 hsmall)
      _ ≤ 2 ^ R * n ^ ((2 * t - 1) * R) := by
        have htwo : 1 ≤ 2 ^ R := one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
        simpa only [one_mul] using Nat.mul_le_mul_right (n ^ ((2 * t - 1) * R)) htwo
  · calc
      n ^ c ≤ n ^ ((2 * t - 1) * R + 1) := Nat.pow_le_pow_right (by omega) hc.1
      _ = n * n ^ ((2 * t - 1) * R) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ 2 ^ R * n ^ ((2 * t - 1) * R) :=
        Nat.mul_le_mul_right _ (hbonus (by omega))
end DeletionCode.WitnessCounting
