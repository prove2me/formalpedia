-- Prove2me | solution 1 for ErdosPosa.restr_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:02.977617+00:00
-- url     : https://prove2.me/submissions/f2a3a3ca-2336-44d3-8738-f609e956def3

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
theorem _root_.solution {H : SimpleGraph V} {S : Set V} {a b : V} :
    (restr H S).Adj a b ↔ H.Adj a b ∧ a ∈ S ∧ b ∈ S := Iff.rfl
end ErdosPosa
