-- Prove2me | solution 1 for ChromaticReconstruction.killP1_psiQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:20:26.211917+00:00
-- url     : https://prove2.me/submissions/35632edf-16d8-4004-8217-f8ea879e38ac

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_killP1_X_of_ne
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (g : MvPolynomial ℕ ℚ) : killP1 (psiQ q g) = psiQ q g := by
  have : killP1.comp (psiQ q) = psiQ q := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, psiQ, rename_X]
    rw [killP1_X_of_ne]
    intro h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp at h
    · have : q * 1 ≤ q * i := Nat.mul_le_mul_left q hi
      omega
  exact congrArg (fun φ => φ g) this
end ChromaticReconstruction
