-- Prove2me | solution 1 for ChromaticReconstruction.eq_empty_of_compType_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:14:45.645535+00:00
-- url     : https://prove2.me/submissions/79427a68-d4f2-44ce-a295-659ef069d912

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
import Theorems.Thm_ChromaticReconstruction_mem_compType
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_compSets_of_reachable
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Finset (Sym2 V)} (hA : ∀ e ∈ A, ¬ e.IsDiag) {s : ℕ}
    (h : compType (A : Set (Sym2 V)) = Multiset.replicate s 1) : A = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := fun h' => hA _ he (by simp [h'])
    have hC := compOf_mem (A : Set (Sym2 V)) x
    have hy : y ∈ compOf (A : Set (Sym2 V)) x :=
      mem_compSets_of_reachable hC (mem_compOf_self _ x) (reachable_of_mem (by exact he))
    have h1 : (compOf (A : Set (Sym2 V)) x).card ∈ compType (A : Set (Sym2 V)) :=
      mem_compType.2 ⟨_, hC, rfl⟩
    rw [h, Multiset.mem_replicate] at h1
    have h2 : ({x, y} : Finset V).card ≤ (compOf (A : Set (Sym2 V)) x).card :=
      card_le_card (by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_compOf_self _ _
        · exact hy)
    rw [card_pair hxy] at h2
    omega
end ChromaticReconstruction
