-- Prove2me | solution 1 for ErdosRubinTaylor.dIn_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:50.814508+00:00
-- url     : https://prove2.me/submissions/0ea7a124-ced4-44d9-8db2-8c70a97c3ed9

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
theorem _root_.solution (G : SimpleGraph V) (T : Set V) (v : V) [DecidablePred (· ∈ T)]
    [DecidableRel G.Adj] : dIn G T v = (univ.filter (fun u => u ∈ T ∧ G.Adj v u)).card := by
  unfold dIn; congr 1; ext; simp
end ErdosRubinTaylor
