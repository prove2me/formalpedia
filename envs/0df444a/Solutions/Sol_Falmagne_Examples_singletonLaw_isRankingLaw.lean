-- Prove2me | solution 1 for Falmagne.Examples.singletonLaw_isRankingLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:46.690793+00:00
-- url     : https://prove2.me/submissions/74977b0a-0931-4e0a-8f89-9fd57415680a

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_singletonRanking_isRanking
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
theorem _root_.solution : IsRankingLaw singletonLaw := by
  refine ⟨?_, ?_, ?_⟩
  · intro l
    simp only [singletonLaw, Finsupp.single_apply]
    split_ifs <;> norm_num
  · intro l hl
    by_cases h : l = singletonRanking
    · subst l
      exact singletonRanking_isRanking
    · simp [singletonLaw, h] at hl
  · simp [singletonLaw]
end Falmagne.Examples
