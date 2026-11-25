-- Prove2me | solution 1 for CliqueMinors.deleteIncidenceSet_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:36.172123+00:00
-- url     : https://prove2.me/submissions/27bbc8b7-ae71-438d-a232-dc539d6cbcec

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
theorem _root_.solution {G : SimpleGraph V} {S : Finset V} {v : V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ a b, (G.deleteIncidenceSet v).Adj a b → a ∈ S.erase v := by
  intro a b h
  rw [deleteIncidenceSet_adj] at h
  exact Finset.mem_erase.2 ⟨h.2.1, hsupp _ _ h.1⟩
end CliqueMinors
