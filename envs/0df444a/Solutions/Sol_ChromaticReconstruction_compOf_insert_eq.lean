-- Prove2me | solution 1 for ChromaticReconstruction.compOf_insert_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:49.521802+00:00
-- url     : https://prove2.me/submissions/0d7da29c-f566-4202-acb4-e715b70da38e

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_compOf_eq_iff
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {u v x y : V}
    (h : compOf (insert s(u, v) A) x = compOf (insert s(u, v) A) y) :
    compOf A x = compOf A y ∨ (compOf A x = compOf A u ∧ compOf A y = compOf A v) ∨
      (compOf A x = compOf A v ∧ compOf A y = compOf A u) := by
  rw [compOf_eq_iff, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hbc
    obtain ⟨hmem, hne⟩ := hbc
    rcases Set.mem_insert_iff.1 hmem with he | hA
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, rfl⟩)
        · exact Or.inl (h1.trans h2)
        · exact Or.inl h1
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨h1, rfl⟩)
        · exact Or.inl h1
        · exact Or.inl (h1.trans h2)
    · have hbc : compOf A b = compOf A c := compOf_eq_iff.2 (reachable_of_mem hA)
      rw [← hbc]; exact ih
end ChromaticReconstruction
