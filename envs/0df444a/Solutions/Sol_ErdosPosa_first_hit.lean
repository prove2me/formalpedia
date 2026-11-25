-- Prove2me | solution 1 for ErdosPosa.first_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:04.799997+00:00
-- url     : https://prove2.me/submissions/4f8ddaf3-7fe9-4aae-8121-2088e4cb3b08

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
theorem _root_.solution {G' : SimpleGraph V} (P : V → Prop) {x w : V} (p : G'.Walk x w) (hw : P w) :
    ∃ w', P w' ∧ ∃ q : G'.Walk x w', (∀ y ∈ q.support, y ≠ w' → ¬ P y) ∧
      (∀ y ∈ q.support, y ∈ p.support) := by
  induction p with
  | nil =>
    refine ⟨_, hw, Walk.nil, ?_, ?_⟩
    · intro y hy hne
      rw [Walk.support_nil, List.mem_singleton] at hy
      exact absurd hy hne
    · intro y hy; exact hy
  | @cons a b c h p ih =>
    by_cases ha : P a
    · refine ⟨a, ha, Walk.nil, ?_, ?_⟩
      · intro y hy hne
        rw [Walk.support_nil, List.mem_singleton] at hy
        exact absurd hy hne
      · intro y hy
        rw [Walk.support_nil, List.mem_singleton] at hy
        rw [hy, Walk.support_cons]
        exact List.mem_cons_self
    · obtain ⟨w', hw', q, hq1, hq2⟩ := ih hw
      refine ⟨w', hw', Walk.cons h q, ?_, ?_⟩
      · intro y hy hne
        rw [Walk.support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ha
        · exact hq1 y hy hne
      · intro y hy
        rw [Walk.support_cons, List.mem_cons] at hy ⊢
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (hq2 y hy)
end ErdosPosa
