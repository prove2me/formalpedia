-- Prove2me | solution 1 for CliqueMinors.coneG_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:34.751719+00:00
-- url     : https://prove2.me/submissions/810520b4-09ee-412a-a0bf-654aecfe2bf7

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {x a b : V} :
    (coneG G x).Adj a b ↔ G.Adj a b ∧ G.Adj x a ∧ G.Adj x b :=
  Iff.rfl
end CliqueMinors
