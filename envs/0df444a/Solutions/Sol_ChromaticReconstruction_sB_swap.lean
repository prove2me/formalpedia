-- Prove2me | solution 1 for ChromaticReconstruction.sB_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:06.1114+00:00
-- url     : https://prove2.me/submissions/538392c6-7b93-4830-853a-3d690a74288e

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_sB_spec
import Theorems.Thm_ChromaticReconstruction_sB_eq
import Theorems.Thm_ChromaticReconstruction_mem_image_rf_iff
import Theorems.Thm_ChromaticReconstruction_not_mem_of_far

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution (hn : 2 * c + 3 ≤ n)
    (hF : F ⊆ (PL n p).edgeFinset) (hb : HasBrk n c F) :
    sB n c (F.image (Sym2.map (rf n c (sB n c F)))) = sB n c F := by
  obtain ⟨hs1, hs2, hbrk, hmin⟩ := sB_spec hb
  set s := sB n c F
  have hs : c + s ≤ n := by omega
  -- the right edge at distance `j`
  have hR : ∀ j, 1 ≤ j → j < s →
      (pe n (c + j) ∈ F.image (Sym2.map (rf n c s)) ↔ pe n (c - j) ∈ F) := by
    intro j hj1 hj2
    rw [pe, mem_image_rf_iff hs hs2 (by omega) (by omega)]
    have e1 : rfv c s (c + j) = c - j + 1 := by unfold rfv; split_ifs <;> omega
    have e2 : rfv c s (c + j + 1) = c - j := by unfold rfv; split_ifs <;> omega
    rw [e1, e2, Sym2.eq_swap]
    rfl
  have hL : ∀ j, 1 ≤ j → j < s →
      (pe n (c - j) ∈ F.image (Sym2.map (rf n c s)) ↔ pe n (c + j) ∈ F) := by
    intro j hj1 hj2
    rw [pe, mem_image_rf_iff hs hs2 (by omega) (by omega)]
    have e1 : rfv c s (c - j) = c + j + 1 := by unfold rfv; split_ifs <;> omega
    have e2 : rfv c s (c - j + 1) = c + j := by unfold rfv; split_ifs <;> omega
    rw [e1, e2, Sym2.eq_swap]
    rfl
  apply sB_eq hs1 hs2
  · refine ⟨?_, ?_⟩
    · by_cases hsc : s = c + 1
      · exact Or.inl hsc
      · right
        rw [pe, mem_image_rf_iff hs hs2 (by omega) (by omega)]
        have e1 : rfv c s (c - s) = c - s := by unfold rfv; split_ifs <;> omega
        have e2 : rfv c s (c - s + 1) = c + s := by unfold rfv; split_ifs <;> omega
        rw [e1, e2]
        exact not_mem_of_far hF (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [pe, mem_image_rf_iff hs hs2 (by omega) (by omega)]
      have e1 : rfv c s (c + s) = c + 1 - s := by unfold rfv; split_ifs <;> omega
      have e2 : rfv c s (c + s + 1) = c + s + 1 := by unfold rfv; split_ifs <;> omega
      rw [e1, e2]
      exact not_mem_of_far hF (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro j hj1 hj2 hbj
    apply hmin j hj1 hj2
    unfold brk at hbj ⊢
    rw [hL j hj1 hj2, hR j hj1 hj2] at hbj
    refine ⟨Or.inr ?_, ?_⟩
    · exact hbj.2
    · rcases hbj.1 with h | h
      · omega
      · exact h
end ChromaticReconstruction
