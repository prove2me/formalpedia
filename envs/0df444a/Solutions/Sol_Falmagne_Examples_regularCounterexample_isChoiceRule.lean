-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexample_isChoiceRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:46.063589+00:00
-- url     : https://prove2.me/submissions/abd4857e-d082-43bf-8774-183819450cd6

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_regularCounterexampleQ_normalized

set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution : IsChoiceRule regularCounterexample := by
  obtain ⟨hnonneg, hoff, hnorm⟩ := regularCounterexampleQ_normalized
  refine ⟨?_, ?_, ?_⟩
  · intro A x
    unfold regularCounterexample
    exact_mod_cast hnonneg A x
  · intro A x hx
    unfold regularCounterexample
    exact_mod_cast hoff A x hx
  · intro A hA
    unfold regularCounterexample
    exact_mod_cast hnorm A hA
end Falmagne.Examples
