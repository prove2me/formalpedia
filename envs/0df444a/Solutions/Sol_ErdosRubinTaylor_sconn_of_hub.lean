-- Prove2me | solution 1 for ErdosRubinTaylor.sconn_of_hub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:22.767966+00:00
-- url     : https://prove2.me/submissions/16d011fe-a507-4e7b-9ec7-daeeb19e181b

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Theorems.Thm_ErdosRubinTaylor_rtg_symm

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable {G : SimpleGraph V} {T T' : Set V}
namespace ErdosRubinTaylor
theorem _root_.solution {a : V} (ha : a ∈ T)
    (h : ∀ v ∈ T, Relation.ReflTransGen (adjIn G T) a v) : SConn G T :=
  ⟨⟨a, ha⟩, fun u hu v hv => (rtg_symm (h u hu)).trans (h v hv)⟩
end ErdosRubinTaylor
