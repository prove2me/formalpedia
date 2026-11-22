-- Prove2me | solution 1 for DeciSigma1.Examples.not_comparable_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:32:22.436389+00:00
-- url     : https://prove2.me/submissions/8f2b7844-9688-4aad-8c63-f32833a4d4ff

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_not_node_le_bot


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models
namespace DeciSigma1.Examples
theorem _root_.solution : ¬ (comparable 2).HoldsIn (fun _ => True) := by
  intro h
  let leaf : PrefixSet 2 := .node (fun _ => .bot)
  rcases h ![.node ![leaf, .bot], .node ![.bot, leaf]] (fun _ => trivial) with hj | hj
  · exact PrefixSet.not_node_le_bot _ ((PrefixSet.node_le_node _ _).mp hj 0)
  · exact PrefixSet.not_node_le_bot _ ((PrefixSet.node_le_node _ _).mp hj 1)
end DeciSigma1.Examples
