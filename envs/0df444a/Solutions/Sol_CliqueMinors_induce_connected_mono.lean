-- Prove2me | solution 1 for CliqueMinors.induce_connected_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:42.558748+00:00
-- url     : https://prove2.me/submissions/fe58dc4c-b982-4f72-ae58-657ec41f35a7

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_reflTransGen_of_step
public import Theorems.Thm_CliqueMinors_induce_connected_of_root
public import Theorems.Thm_CliqueMinors_reflTransGen_of_connected

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {G G' : SimpleGraph V} (hle : G' ≤ G) {B : Finset V}
    (h : (G'.induce (B : Set V)).Connected) : (G.induce (B : Set V)).Connected := by
  obtain ⟨⟨r, hr⟩⟩ := h.nonempty
  exact induce_connected_of_root G _ r hr fun v hv =>
    reflTransGen_of_step (fun a b hab => ReflTransGen.single ⟨hab.1, hab.2.1, hle hab.2.2⟩)
      (reflTransGen_of_connected h hr hv)
end CliqueMinors
