-- Prove2me | solution 1 for DeciSigma1.Examples.comparable_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:26:02.726563+00:00
-- url     : https://prove2.me/submissions/e390a0f0-1048-4aff-baa9-36b7bba87a3e

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
public import Theorems.Thm_DeciSigma1_Examples_unary_le_total


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models
namespace DeciSigma1.Examples
theorem _root_.solution : (comparable 1).HoldsIn (fun _ => True) :=
  fun ρ _ => unary_le_total (ρ 0) (ρ 1)
end DeciSigma1.Examples
