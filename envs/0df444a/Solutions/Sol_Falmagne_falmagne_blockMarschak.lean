-- Prove2me | solution 1 for Falmagne.falmagne_blockMarschak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:40.740678+00:00
-- url     : https://prove2.me/submissions/fdb6e942-aee6-47cd-a3b6-8b45cf3bb885

module
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Definitions.Def_EconomicsNextProof_Flow
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Theorems.Thm_Falmagne_randomUtility_necessary
public import Theorems.Thm_Falmagne_randomUtility_sufficient

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
namespace Falmagne
theorem _root_.solution {p : Finset X → X → ℝ} (hp : IsChoiceRule p) :
    RandomUtilityRepresentable p ↔ BlockMarschakNonnegative p :=
  ⟨randomUtility_necessary, randomUtility_sufficient hp⟩
end Falmagne
