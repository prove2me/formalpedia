-- Prove2me | solution 1 for CliqueMinors.reflTransGen_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:02.383595+00:00
-- url     : https://prove2.me/submissions/96cab0cb-daaa-4e99-b141-93871e656b0e

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {B : Finset V}
    (h : (G.induce (B : Set V)).Connected) {u v : V} (hu : u ∈ B) (hv : v ∈ B) :
    ReflTransGen (InAdj G B) u v := by
  have := (reachable_iff_reflTransGen _ _).1 (h.preconnected ⟨u, hu⟩ ⟨v, hv⟩)
  exact this.lift Subtype.val (fun a b hab => ⟨a.2, b.2, hab⟩)
end CliqueMinors
