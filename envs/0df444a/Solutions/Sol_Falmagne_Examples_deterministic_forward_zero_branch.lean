-- Prove2me | solution 1 for Falmagne.Examples.deterministic_forward_zero_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:16.377362+00:00
-- url     : https://prove2.me/submissions/4240dd72-bee0-4b76-afd8-dca91e216d9f

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
    rankingChoice forwardRanking univ (1 : Fin 4) = 0 := by
  have h : ¬ ((1 : Fin 4) ∈ univ ∧ univ ⊆ lowerContour forwardRanking 1) := by
    decide +kernel
  simp only [rankingChoice, if_neg h]
end Falmagne.Examples
