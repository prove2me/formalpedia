-- Prove2me | solution 1 for ErdosRubinTaylor.rtg_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:53.064003+00:00
-- url     : https://prove2.me/submissions/1d57f794-f14e-4a1f-8886-98f268b4766a

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
theorem _root_.solution {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) (hu : u ∈ T) : v ∈ T := by
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2.1
end ErdosRubinTaylor
