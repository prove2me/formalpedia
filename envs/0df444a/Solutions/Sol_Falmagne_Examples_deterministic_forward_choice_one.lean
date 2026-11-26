-- Prove2me | solution 1 for Falmagne.Examples.deterministic_forward_choice_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:11.639799+00:00
-- url     : https://prove2.me/submissions/9e27e53a-ae23-4507-85d8-90e934a40798

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_rankingChoice_eq_one_iff


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    rankingChoice forwardRanking univ (0 : Fin 4) = 1 := by
  apply rankingChoice_eq_one_iff.mpr
  decide +kernel
end Falmagne.Examples
