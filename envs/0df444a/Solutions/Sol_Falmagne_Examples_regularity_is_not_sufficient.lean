-- Prove2me | solution 1 for Falmagne.Examples.regularity_is_not_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:43.111703+00:00
-- url     : https://prove2.me/submissions/7f51fa62-9b06-4fee-8a83-ef4ad5e267ff

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_regularCounterexample_isChoiceRule
public import Theorems.Thm_Falmagne_Examples_regularCounterexample_regular
public import Theorems.Thm_Falmagne_Examples_regularCounterexample_not_representable

set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    IsChoiceRule regularCounterexample ∧
    (∀ A B : Finset (Fin 4), A ⊆ B → ∀ x ∈ A,
      regularCounterexample B x ≤ regularCounterexample A x) ∧
    ¬ RandomUtilityRepresentable regularCounterexample :=
  ⟨regularCounterexample_isChoiceRule, regularCounterexample_regular,
    regularCounterexample_not_representable⟩
end Falmagne.Examples
