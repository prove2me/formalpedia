-- Prove2me | solution 1 for ErdosRubinTaylor.adjIn_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:25.924151+00:00
-- url     : https://prove2.me/submissions/1557579a-1b5c-4104-b3b9-ec945d605b3b

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
theorem _root_.solution {u v : V} (h : adjIn G T u v) : adjIn G T v u := ⟨h.2.1, h.1, h.2.2.symm⟩
end ErdosRubinTaylor
