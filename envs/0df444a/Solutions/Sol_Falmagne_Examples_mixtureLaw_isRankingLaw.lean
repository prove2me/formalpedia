-- Prove2me | solution 1 for Falmagne.Examples.mixtureLaw_isRankingLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:48.078064+00:00
-- url     : https://prove2.me/submissions/d3d655e3-7fe8-4395-97cd-ac4fdb9e5e32

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_forwardRanking_isRanking
public import Theorems.Thm_Falmagne_Examples_reverseRanking_isRanking
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
theorem _root_.solution : IsRankingLaw mixtureLaw := by
  refine ⟨?_, ?_, ?_⟩
  · intro l
    simp only [mixtureLaw, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  · intro l hl
    by_cases hf : l = forwardRanking
    · subst l
      exact forwardRanking_isRanking
    by_cases hr : l = reverseRanking
    · subst l
      exact reverseRanking_isRanking
    simp [mixtureLaw, Finsupp.mem_support_iff, hf, hr] at hl
  · simp [mixtureLaw, Finsupp.sum_add_index]
    norm_num
end Falmagne.Examples
