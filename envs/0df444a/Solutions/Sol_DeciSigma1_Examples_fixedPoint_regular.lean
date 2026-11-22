-- Prove2me | solution 1 for DeciSigma1.Examples.fixedPoint_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:32:51.276839+00:00
-- url     : https://prove2.me/submissions/f9b936b5-1a2b-4211-9bfa-8d3ae21f5543

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
public import Theorems.Thm_DeciSigma1_Full_Logic_holds_eq_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_subtree_fn
public import Theorems.Thm_DeciSigma1_Semantics_fullTree_eq_node


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models
namespace DeciSigma1.Examples
theorem _root_.solution : fixedPoint.HoldsIn RegularTop (fun _ => true) := by
  refine ⟨fun _ => fullTree, ?_, ?_⟩
  · intro _
    apply (Set.finite_singleton (fullTree : Semantics.Tree 1)).subset
    rintro u ⟨w, hw⟩
    apply Tree.ext
    funext v
    rw [Tree.subtree_fn hw]
    rfl
  · exact (DeciSigma1.Full.Logic.holds_eq_iff _ _ _ _).mpr (fullTree_eq_node (n := 1))
end DeciSigma1.Examples
