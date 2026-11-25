-- Prove2me | solution 1 for DegreeSequences.degree_fin_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:37:03.246492+00:00
-- url     : https://prove2.me/submissions/b6cfab91-c713-4b85-8e5f-67be147c7b0d

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (G : SimpleGraph (Fin (m + 1))) [DecidableRel G.Adj]
    (v : Fin (m + 1)) :
    G.degree v = (if G.Adj v 0 then 1 else 0) + #{w : Fin m | G.Adj v w.succ} := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Fin.card_filter_univ_succ']
end DegreeSequences
