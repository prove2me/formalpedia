-- Prove2me | solution 1 for ErdosRubinTaylor.SConn.rtg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:38.219337+00:00
-- url     : https://prove2.me/submissions/da9f78ee-8554-4702-8b02-7e0613383dc7

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable {G : SimpleGraph V} {T T' : Set V}
namespace ErdosRubinTaylor
namespace SConn
theorem _root_.solution (h : SConn G T) {u v : V} (hu : u ∈ T) (hv : v ∈ T) :
    Relation.ReflTransGen (adjIn G T) u v := h.2 u hu v hv
end SConn
end ErdosRubinTaylor
