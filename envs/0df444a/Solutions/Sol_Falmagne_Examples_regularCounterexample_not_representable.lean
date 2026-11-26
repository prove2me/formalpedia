-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexample_not_representable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:21.827704+00:00
-- url     : https://prove2.me/submissions/754ba4f5-4678-4b12-8718-0d96ea19baeb

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_regularCounterexample_bm_negative
public import Theorems.Thm_Falmagne_blockMarschak_necessary
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
    ¬ ∃ w : RankingLaw (Fin 4), IsRankingLaw w ∧ Represents w regularCounterexample := by
  rintro ⟨w, hw, hp⟩
  have h := blockMarschak_necessary hw hp (0 : Fin 4) {0} (by simp)
  change 0 ≤ blockMarschak regularCounterexample (0 : Fin 4) {0} at h
  linarith [regularCounterexample_bm_negative]
end Falmagne.Examples
