-- Prove2me | solution 1 for CliqueMinors.card_edges_deleteIncidenceSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:41.942043+00:00
-- url     : https://prove2.me/submissions/ed2fc9ae-b548-48e8-a253-c1c615259c4e

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
theorem _root_.solution (G G' : SimpleGraph V) (v : V)
    (hG' : G' = G.deleteIncidenceSet v) :
    G.edgeFinset.card = G'.edgeFinset.card + G.degree v := by
  subst hG'
  have h1 := card_edgeFinset_deleteIncidenceSet G v
  have h2 : G.degree v ≤ G.edgeFinset.card := by
    rw [← card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (G.incidenceFinset_subset v)
  convert (Nat.sub_add_cancel h2).symm using 3
  convert h1 using 2
  ext e; simp
end CliqueMinors
