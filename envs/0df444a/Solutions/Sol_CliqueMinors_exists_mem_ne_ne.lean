-- Prove2me | solution 1 for CliqueMinors.exists_mem_ne_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:53.117619+00:00
-- url     : https://prove2.me/submissions/f8e3585a-73c7-4b58-9354-ff2319a93eb7

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
theorem _root_.solution {s : Finset V} (h : 3 ≤ s.card) (p q : V) :
    ∃ z ∈ s, z ≠ p ∧ z ≠ q := by
  have h1 := Finset.pred_card_le_card_erase (s := s) (a := p)
  have h2 := Finset.pred_card_le_card_erase (s := s.erase p) (a := q)
  obtain ⟨z, hz⟩ := Finset.card_pos.1 (show 0 < ((s.erase p).erase q).card by omega)
  simp only [Finset.mem_erase] at hz
  exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
end CliqueMinors
