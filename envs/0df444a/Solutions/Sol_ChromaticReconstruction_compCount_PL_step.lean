-- Prove2me | solution 1 for ChromaticReconstruction.compCount_PL_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:26.271017+00:00
-- url     : https://prove2.me/submissions/d2973e3d-729a-4cae-b168-aa045701b1ab

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_psiMap_spec
import Theorems.Thm_ChromaticReconstruction_PL_isTree
import Theorems.Thm_ChromaticReconstruction_card_compSets_add_card_of_isTree
import Theorems.Thm_ChromaticReconstruction_card_compType


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution (hn : 2 * c + 3 ≤ n) (μ : Multiset ℕ)
    (hμ : n - c ≤ Multiset.card μ) : compCount (PL n c) μ = compCount (PL n (c + 1)) μ := by
  have hsmall : ∀ q, q < n → ∀ F : Finset (Sym2 (Fin (n + 1))), F ⊆ (PL n q).edgeFinset →
      compType (F : Set (Sym2 (Fin (n + 1)))) = μ → F.card ≤ c + 1 := by
    intro q hq F hF hμF
    have h1 := card_compSets_add_card_of_isTree (PL_isTree hq) hF
    have h2 := card_compType (F : Set (Sym2 (Fin (n + 1))))
    rw [hμF] at h2
    rw [Fintype.card_fin] at h1
    omega
  have e1 : 2 * c + 1 - c = c + 1 := by omega
  have e2 : 2 * c + 1 - (c + 1) = c := by omega
  unfold compCount
  refine card_bij' (fun F _ => psiMap n c c F) (fun F _ => psiMap n c (c + 1) F) ?_ ?_ ?_ ?_
  · intro F hF
    rw [mem_filter, mem_powerset] at hF ⊢
    have := psiMap_spec hn (Or.inl rfl) hF.1 (hsmall c (by omega) F hF.1 hF.2)
    rw [e1] at this
    exact ⟨this.1, this.2.1.trans hF.2⟩
  · intro F hF
    rw [mem_filter, mem_powerset] at hF ⊢
    have := psiMap_spec hn (Or.inr rfl) hF.1 (hsmall (c + 1) (by omega) F hF.1 hF.2)
    rw [e2] at this
    exact ⟨this.1, this.2.1.trans hF.2⟩
  · intro F hF
    rw [mem_filter, mem_powerset] at hF
    have := psiMap_spec hn (Or.inl rfl) hF.1 (hsmall c (by omega) F hF.1 hF.2)
    rw [e1] at this
    exact this.2.2
  · intro F hF
    rw [mem_filter, mem_powerset] at hF
    have := psiMap_spec hn (Or.inr rfl) hF.1 (hsmall (c + 1) (by omega) F hF.1 hF.2)
    rw [e2] at this
    exact this.2.2
end ChromaticReconstruction
