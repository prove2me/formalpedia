-- Prove2me | solution 1 for Falmagne.Examples.mixture_full_menu_middle_probability_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:38.275837+00:00
-- url     : https://prove2.me/submissions/c0e99469-444b-4e45-a111-24ae4ca35ddc

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
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
    mixtureChoice univ (1 : Fin 4) = 0 := by
  have hf : ¬ ((1 : Fin 4) ∈ univ ∧ univ ⊆ lowerContour forwardRanking 1) := by
    decide +kernel
  have hr : ¬ ((1 : Fin 4) ∈ univ ∧ univ ⊆ lowerContour reverseRanking 1) := by
    decide +kernel
  simp only [mixtureChoice, rankingChoice, if_neg hf, if_neg hr]
  norm_num
end Falmagne.Examples
