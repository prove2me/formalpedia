-- Prove2me | solution 1 for DeciSigma1.Examples.postFixedPoint_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:32:30.290768+00:00
-- url     : https://prove2.me/submissions/2af7f0e6-3350-46aa-b29e-343ba8a3678e

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
public import Theorems.Thm_DeciSigma1_Semantics_isRegularTree_univ


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models
namespace DeciSigma1.Examples
theorem _root_.solution : postFixedPoint.HoldsIn IsRegularTree :=
  ⟨fun _ => PrefixSet.univ, fun _ => isRegularTree_univ, PrefixSet.node_univ.le⟩
end DeciSigma1.Examples
