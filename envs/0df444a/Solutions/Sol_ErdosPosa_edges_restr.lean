-- Prove2me | solution 1 for ErdosPosa.edges_restr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:01.355584+00:00
-- url     : https://prove2.me/submissions/e95e19f7-64f4-43cc-82c8-8ac1680145c4

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {G : SimpleGraph V} {X : Set V} {a b : V} (p : (restr G X).Walk a b)
    {e : Sym2 V} (he : e ∈ p.edges) : ∃ c d, e = s(c, d) ∧ c ≠ d ∧ c ∈ X ∧ d ∈ X := by
  have := p.edges_subset_edgeSet he
  induction e using Sym2.ind with
  | _ c d => exact ⟨c, d, rfl, this.1.ne, this.2.1, this.2.2⟩
end ErdosPosa
