-- Prove2me | solution 1 for DegreeSequences.hhExtend_adj_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:57:16.279065+00:00
-- url     : https://prove2.me/submissions/21fdedac-517a-4f54-99a8-16524e841403

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
    (j k : Fin m) : (hhExtend d H).Adj j.succ k.succ ↔ H.Adj j k := by
  simp only [hhExtend, fromRel_adj, ne_eq, Fin.succ_inj, Fin.succ_ne_zero, false_and,
    exists_and_left, exists_eq_left', false_or]
  exact ⟨fun h => h.2.elim id fun h' => h'.symm, fun h => ⟨H.ne_of_adj h, Or.inl h⟩⟩
end DegreeSequences
