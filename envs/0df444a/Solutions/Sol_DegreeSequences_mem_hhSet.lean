-- Prove2me | solution 1 for DegreeSequences.mem_hhSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:37:34.894884+00:00
-- url     : https://prove2.me/submissions/ebf8b296-aa4a-4b14-b0e3-81b3ff551a11

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (v : Fin (m + 1)) :
    v ∈ hhSet d ↔ v ≠ 0 ∧ v.val < d 0 + 1 := by
  simp [hhSet]
end DegreeSequences
