-- Prove2me | solution 1 for ChromaticReconstruction.hasBrk_of_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:14:09.190211+00:00
-- url     : https://prove2.me/submissions/d5b9e1f5-200f-4859-a293-0f9a2e86af15

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_pe_inj
import Theorems.Thm_ChromaticReconstruction_pe_ne_lf
import Theorems.Thm_ChromaticReconstruction_vx_val
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.vx_val



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {p : ℕ} (hn : 2 * c + 3 ≤ n) (hp : p ≤ c + 1)
    {F : Finset (Sym2 (Fin (n + 1)))} (hl : lf n p ∈ F)
    (hcard : F.card ≤ c + 1) : HasBrk n c F := by
  by_contra hno
  have hno' : ∀ j, 1 ≤ j → j ≤ c + 1 → ¬ brk n c F j := fun j h1 h2 hb => hno ⟨j, h1, h2, hb⟩
  let g : ℕ → Sym2 (Fin (n + 1)) := fun j =>
    if j ≤ c ∧ pe n (c - j) ∈ F then pe n (c - j) else pe n (c + j)
  have hg : ∀ j ∈ Icc 1 (c + 1), g j ∈ F.erase (lf n p) := by
    intro j hj
    rw [mem_Icc] at hj
    have hb := hno' j hj.1 hj.2
    unfold brk at hb
    rw [mem_erase]
    simp only [g]
    split_ifs with h
    · exact ⟨pe_ne_lf (by omega) (by omega), h.2⟩
    · refine ⟨pe_ne_lf (by omega) (by omega), ?_⟩
      by_contra h'
      apply hb
      refine ⟨?_, h'⟩
      by_cases hj' : j = c + 1
      · exact Or.inl hj'
      · exact Or.inr fun h'' => h ⟨by omega, h''⟩
  have hinj : Set.InjOn g (Icc 1 (c + 1) : Finset ℕ) := by
    intro i hi j hj hij
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    simp only [g] at hij
    split_ifs at hij with h1 h2 h2
    · rw [pe_inj (by omega) (by omega)] at hij; omega
    · rw [pe_inj (by omega) (by omega)] at hij; omega
    · rw [pe_inj (by omega) (by omega)] at hij; omega
    · rw [pe_inj (by omega) (by omega)] at hij; omega
  have := card_le_card_of_injOn g (fun j hj => hg j hj) hinj
  rw [Nat.card_Icc, card_erase_of_mem hl] at this
  omega
end ChromaticReconstruction
