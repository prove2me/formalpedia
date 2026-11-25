-- Prove2me | solution 1 for DegreeSequences.bot_isGraphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:58:11.866556+00:00
-- url     : https://prove2.me/submissions/9dbe6c35-f351-4a92-bb5a-b3b022692c10

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (h : ∀ i, d i = 0) : IsGraphic d :=
  ⟨⊥, inferInstance, fun i => by rw [bot_degree, h]⟩
end DegreeSequences
