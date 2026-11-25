-- Prove2me | solution 1 for CliqueMinors.contractG_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:21.097476+00:00
-- url     : https://prove2.me/submissions/a31ec5c3-01e1-430b-a871-2668175746ba

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
theorem _root_.solution {G : SimpleGraph V} {x y a b : V} :
    (contractG G x y).Adj a b ↔
      a ≠ b ∧ a ≠ y ∧ b ≠ y ∧ (G.Adj a b ∨ (a = x ∧ G.Adj y b) ∨ (b = x ∧ G.Adj y a)) :=
  Iff.rfl
end CliqueMinors
