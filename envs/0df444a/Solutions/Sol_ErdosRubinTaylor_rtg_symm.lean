-- Prove2me | solution 1 for ErdosRubinTaylor.rtg_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:17.212029+00:00
-- url     : https://prove2.me/submissions/e49ef0b6-3ce1-4187-af75-c037fb2bac22

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Theorems.Thm_ErdosRubinTaylor_adjIn_symm

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable {G : SimpleGraph V} {T T' : Set V}
namespace ErdosRubinTaylor
theorem _root_.solution {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) :
    Relation.ReflTransGen (adjIn G T) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (adjIn_symm hbc) ih
end ErdosRubinTaylor
