-- Prove2me | solution 1 for ChromaticReconstruction.pderiv_opD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:18.09328+00:00
-- url     : https://prove2.me/submissions/6c3f0568-6a5f-47da-80d9-642ed1c62a96

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_not_dvd_mul_sub_one
import Theorems.Thm_ChromaticReconstruction_pderiv_psiQ_eq_zero
import Theorems.Thm_ChromaticReconstruction_killP1_psiQ
import Theorems.Thm_ChromaticReconstruction_killP1_X
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
theorem _root_.solution (q N r : ℕ) (hq : 2 ≤ q) (hrN : r < N) (hr : 1 ≤ r) (hqr : q * r - 1 ≠ 1)
    (f : MvPolynomial ℕ ℚ) :
    pderiv (q * r - 1) (opD q N f) = C (r : ℚ) * psiQ q (pderiv r f) := by
  unfold opD
  simp only [map_sum, map_mul, algHom_C, algebraMap_eq, killP1_psiQ hq]
  rw [sum_eq_single r]
  · rw [Derivation.leibniz, Derivation.leibniz, pderiv_psiQ_eq_zero
      (not_dvd_mul_sub_one hq hr), pderiv_C, killP1_X_of_ne hqr, pderiv_X_self]
    simp only [smul_eq_mul]
    ring
  · intro s _ hs
    rw [Derivation.leibniz, Derivation.leibniz, pderiv_psiQ_eq_zero
      (not_dvd_mul_sub_one hq hr), pderiv_C]
    have : pderiv (q * r - 1) (killP1 (X (q * s - 1))) = 0 := by
      rw [killP1_X]
      split_ifs
      · simp
      · rw [pderiv_X_of_ne]
        intro h
        rcases Nat.eq_zero_or_pos s with rfl | hs'
        · have : 1 ≤ q * r := Nat.one_le_iff_ne_zero.2 (by positivity)
          simp at h
          have : q * 1 ≤ q * r := Nat.mul_le_mul_left q hr
          omega
        · have h1 : 1 ≤ q * s := Nat.one_le_iff_ne_zero.2 (by positivity)
          have h2 : 1 ≤ q * r := Nat.one_le_iff_ne_zero.2 (by positivity)
          have : q * s = q * r := by omega
          exact hs (Nat.eq_of_mul_eq_mul_left (by omega) this)
    rw [this]
    simp
  · intro h
    exact absurd (mem_range.2 hrN) h
end ChromaticReconstruction
