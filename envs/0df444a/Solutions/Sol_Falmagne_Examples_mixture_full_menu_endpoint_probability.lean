-- Prove2me | solution 1 for Falmagne.Examples.mixture_full_menu_endpoint_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:04.961627+00:00
-- url     : https://prove2.me/submissions/fcf8835a-c9de-4d99-b68c-9de4a61c3d11

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
    mixtureChoice univ (0 : Fin 4) = 1 / 2 := by
  have hf : (0 : Fin 4) ∈ univ ∧ univ ⊆ lowerContour forwardRanking 0 := by
    decide +kernel
  have hr : ¬ ((0 : Fin 4) ∈ univ ∧ univ ⊆ lowerContour reverseRanking 0) := by
    decide +kernel
  simp only [mixtureChoice, rankingChoice, if_pos hf, if_neg hr]
  norm_num
end Falmagne.Examples
