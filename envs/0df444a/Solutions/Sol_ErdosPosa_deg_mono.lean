-- Prove2me | solution 1 for ErdosPosa.deg_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:36.652587+00:00
-- url     : https://prove2.me/submissions/986a557c-2ec9-4531-b0ac-83cd74a38294

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
namespace ErdosPosa
theorem _root_.solution [Finite V] {H₁ H : SimpleGraph V} (h : H₁ ≤ H) (v : V) : deg H₁ v ≤ deg H v :=
  Set.ncard_le_ncard (fun _ hw => h hw) (Set.toFinite _)
end ErdosPosa
