-- Prove2me | solution 1 for ErdosPosa.cyc_of_cyc_restr_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:41.36166+00:00
-- url     : https://prove2.me/submissions/80cd5759-af94-4d3e-88e7-70c260b02929

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable {H₀ : SimpleGraph V} {T : Set V}
namespace ErdosPosa
theorem _root_.solution {A : Set V} (h : Cyc (restr H₀ Tᶜ) A) : Cyc H₀ (A \ T) := by
  intro hac
  apply h
  refine hac.anti ?_
  intro a b hab
  exact ⟨hab.1.1, ⟨hab.2.1, hab.1.2.1⟩, ⟨hab.2.2, hab.1.2.2⟩⟩
end ErdosPosa
