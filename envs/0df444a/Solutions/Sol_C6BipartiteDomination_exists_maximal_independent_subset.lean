-- Prove2me | solution 1 for C6BipartiteDomination.exists_maximal_independent_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:51.1731+00:00
-- url     : https://prove2.me/submissions/afaa7b78-8580-49a3-9870-5e577361bc0e

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (A : Finset V) :
    ∃ I ⊆ A, Independent G I ∧
      ∀ ⦃a⦄, a ∈ A → a ∉ I → ∃ i ∈ I, G.Adj i a := by
  classical
  let indeps := A.powerset.filter (Independent G)
  have hempty : (∅ : Finset V) ∈ indeps := by
    simp [indeps, Independent]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image indeps Finset.card ⟨∅, hempty⟩
  have hIsub : I ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  have hIind : Independent G I := (Finset.mem_filter.mp hI).2
  refine ⟨I, hIsub, hIind, ?_⟩
  intro a ha haI
  by_contra hno
  push Not at hno
  have hinsertSub : insert a I ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hxI
    · exact ha
    · exact hIsub hxI
  have hinsertInd : Independent G (insert a I) := by
    intro u v hu hv hadj
    simp only [Finset.mem_insert] at hu hv
    rcases hu with rfl | huI <;> rcases hv with rfl | hvI
    · exact G.irrefl hadj
    · exact (hno v hvI) hadj.symm
    · exact (hno u huI) hadj
    · exact hIind huI hvI hadj
  have hinsertMem : insert a I ∈ indeps := by
    simp [indeps, hinsertSub, hinsertInd]
  have hle := hmax (insert a I) hinsertMem
  have hlt : I.card < (insert a I).card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_insert a I, by
    intro heq
    have : a ∈ insert a I := by simp
    rw [← heq] at this
    exact haI this
  ⟩)
  omega
end C6BipartiteDomination
