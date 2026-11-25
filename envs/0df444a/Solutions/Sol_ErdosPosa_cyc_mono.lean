-- Prove2me | solution 1 for ErdosPosa.cyc_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:42.605411+00:00
-- url     : https://prove2.me/submissions/4fcf65f4-07bf-4bfe-bcf9-cd97e9c7c1d2

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {H H' : SimpleGraph V} {S S' : Set V} (h : Cyc H S) (hH : H ≤ H')
    (hS : S ⊆ S') : Cyc H' S' := by
  intro hac
  apply h
  refine hac.anti ?_
  intro a b hab
  exact ⟨hH hab.1, hS hab.2.1, hS hab.2.2⟩
end ErdosPosa
