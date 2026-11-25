-- Prove2me | solution 1 for ErdosGirth.edgesIn_subset_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:06.029899+00:00
-- url     : https://prove2.me/submissions/99c7cd64-db3d-4853-aeca-4983c5b49ee7

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} (T : Finset (Fin m)) : edgesIn T ⊆ pairs m := by
  intro e he
  simp only [edgesIn, mem_image, mem_offDiag] at he
  obtain ⟨⟨a, b⟩, ⟨-, -, hab⟩, rfl⟩ := he
  simpa [pairs] using hab
end ErdosGirth
