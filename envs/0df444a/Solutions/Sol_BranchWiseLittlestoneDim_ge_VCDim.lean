-- Prove2me | solution 1 for BranchWiseLittlestoneDim_ge_VCDim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:53.977552+00:00
-- url     : https://prove2.me/submissions/822efe4f-5c57-4b60-af97-b626c5df8d12

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Theorems.Thm_MistakeTree_fromList_depth
public import Theorems.Thm_MistakeTree_fromList_shattered

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) : VCDim X C ≤ BranchWiseLittlestoneDim X C := by
  classical
  unfold VCDim BranchWiseLittlestoneDim
  apply iSup₂_le
  intro S hS
  let T := MistakeTree.fromList S.toList
  have hd : T.depth = S.card := by
    simp only [T, MistakeTree.fromList_depth]
    exact S.length_toList
  have ht : T.isShattered X C :=
    MistakeTree.fromList_shattered _ S.nodup_toList (by rwa [Finset.toList_toFinset])
  exact hd ▸ le_iSup₂_of_le T ht le_rfl
