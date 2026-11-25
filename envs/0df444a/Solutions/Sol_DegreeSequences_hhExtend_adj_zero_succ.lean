-- Prove2me | solution 1 for DegreeSequences.hhExtend_adj_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:57:05.812297+00:00
-- url     : https://prove2.me/submissions/a306399f-3c6c-4d93-b98f-bc2266d79250

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m))
    (j : Fin m) : (hhExtend d H).Adj 0 j.succ ↔ j.val < d 0 := by
  simp [hhExtend, (Fin.succ_ne_zero _).symm]
end DegreeSequences
