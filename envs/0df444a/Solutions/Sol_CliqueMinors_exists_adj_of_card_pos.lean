-- Prove2me | solution 1 for CliqueMinors.exists_adj_of_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:42.950122+00:00
-- url     : https://prove2.me/submissions/79fc086f-c32d-4573-b45e-95c395844c09

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
theorem _root_.solution {G : SimpleGraph V} (h : 0 < G.edgeFinset.card) :
    ∃ a b, G.Adj a b := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, by simpa using he⟩
end CliqueMinors
