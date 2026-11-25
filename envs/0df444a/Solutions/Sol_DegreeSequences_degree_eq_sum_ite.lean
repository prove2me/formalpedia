-- Prove2me | solution 1 for DegreeSequences.degree_eq_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:37:09.758849+00:00
-- url     : https://prove2.me/submissions/6c056560-bf38-4e82-9f6b-44b14a5055ac

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ w, if G.Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]
end DegreeSequences
