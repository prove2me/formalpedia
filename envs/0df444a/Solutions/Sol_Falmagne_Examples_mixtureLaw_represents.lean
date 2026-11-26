-- Prove2me | solution 1 for Falmagne.Examples.mixtureLaw_represents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:49.931183+00:00
-- url     : https://prove2.me/submissions/475d370e-9694-4c77-9e6d-708b95e222cb

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
theorem _root_.solution : Represents mixtureLaw mixtureChoice := by
  intro A x
  simp [mixtureChoice, mixtureLaw, Finsupp.sum_add_index, add_mul]
end Falmagne.Examples
