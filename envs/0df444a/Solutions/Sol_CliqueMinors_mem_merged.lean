-- Prove2me | solution 1 for CliqueMinors.mem_merged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:20.953566+00:00
-- url     : https://prove2.me/submissions/8244045e-4a5d-40ce-91c0-6a4756a0aa2f

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
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {x y t : V} :
    t ∈ ((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y ↔
      t ≠ y ∧ t ≠ x ∧ (G.Adj x t ∨ G.Adj y t) := by
  simp
end CliqueMinors
