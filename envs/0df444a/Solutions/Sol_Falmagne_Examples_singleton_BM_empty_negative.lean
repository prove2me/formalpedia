-- Prove2me | solution 1 for Falmagne.Examples.singleton_BM_empty_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:41.731865+00:00
-- url     : https://prove2.me/submissions/23853be4-0e4a-4c29-a0bd-7dbaf61863da

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_singleton_isChoiceRule
public import Theorems.Thm_Falmagne_Examples_singleton_probability_one
public import Theorems.Thm_Falmagne_blockMarschak_not_mem
public import Theorems.Thm_Falmagne_blockMarschak_univ
public import Theorems.Thm_Falmagne_mem_edgeSupport
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_rankingEdge_eq_zero_of_not_mem
attribute [local simp] Falmagne.mem_edgeSupport
attribute [local simp] Falmagne.mem_lowerContour
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.rankingEdge_eq_zero_of_not_mem



set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    blockMarschak (rankingChoice singletonRanking) (0 : Fin 1) ∅ = -1 := by
  rw [blockMarschak_not_mem _ singleton_isChoiceRule ∅ 0 (by simp)]
  have hu : ({0} : Finset (Fin 1)) = univ := by decide +kernel
  simp only [insert_empty_eq, hu, blockMarschak_univ]
  have hp : rankingChoice singletonRanking (univ : Finset (Fin 1)) 0 = 1 := by
    rw [← hu]
    exact singleton_probability_one
  rw [hp]
end Falmagne.Examples
