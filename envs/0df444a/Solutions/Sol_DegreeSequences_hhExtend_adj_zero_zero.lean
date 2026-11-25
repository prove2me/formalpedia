-- Prove2me | solution 1 for DegreeSequences.hhExtend_adj_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:56:56.925029+00:00
-- url     : https://prove2.me/submissions/2ab49d90-4d89-4e22-bd0e-3dfb8a580941

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m)) :
    ¬ (hhExtend d H).Adj 0 0 := (hhExtend d H).loopless.irrefl 0
end DegreeSequences
