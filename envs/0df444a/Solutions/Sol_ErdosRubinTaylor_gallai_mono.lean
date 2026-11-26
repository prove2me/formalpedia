-- Prove2me | solution 1 for ErdosRubinTaylor.gallai_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:40.263551+00:00
-- url     : https://prove2.me/submissions/4a572e4e-fbff-4b45-a976-5d9bbbe84a7e

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
namespace ErdosRubinTaylor
theorem _root_.solution {T T' : Set V} (h : Gallai G T) (hsub : T' ⊆ T) : Gallai G T' :=
  fun S hS => h S (hS.trans hsub)
end ErdosRubinTaylor
