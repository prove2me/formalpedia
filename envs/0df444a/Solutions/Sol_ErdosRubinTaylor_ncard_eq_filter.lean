-- Prove2me | solution 1 for ErdosRubinTaylor.ncard_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:21.44209+00:00
-- url     : https://prove2.me/submissions/9aeccad6-434f-40e1-8a7c-604c590e25f1

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
namespace ErdosRubinTaylor
theorem _root_.solution (T : Set V) [DecidablePred (· ∈ T)] :
    T.ncard = (univ.filter (· ∈ T)).card := by
  rw [← Set.ncard_coe_finset]; congr; ext; simp
end ErdosRubinTaylor
