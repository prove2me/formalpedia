-- Prove2me | solution 1 for ErdosPosa.support_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:05.470792+00:00
-- url     : https://prove2.me/submissions/48dd98b1-b627-4da2-9dcb-9b382dd292d5

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
theorem _root_.solution {G' : SimpleGraph V} {S : Set V} (hS : ∀ a b, G'.Adj a b → a ∈ S → b ∈ S)
    {u v : V} (p : G'.Walk u v) (hu : u ∈ S) : v ∈ S := by
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hS _ _ h hu)
end ErdosPosa
