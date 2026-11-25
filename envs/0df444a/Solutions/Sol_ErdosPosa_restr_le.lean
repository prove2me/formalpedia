-- Prove2me | solution 1 for ErdosPosa.restr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:12.620816+00:00
-- url     : https://prove2.me/submissions/563b2cd3-54b8-43fb-a2ba-9b460214eaf4

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution (G : SimpleGraph V) (X : Set V) : restr G X ≤ G := fun _ _ h => h.1
end ErdosPosa
