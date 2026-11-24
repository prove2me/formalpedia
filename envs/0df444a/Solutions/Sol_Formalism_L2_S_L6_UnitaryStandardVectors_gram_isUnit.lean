-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.gram_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:52.205842+00:00
-- url     : https://prove2.me/submissions/22c99be9-a715-44e1-b537-9f62bc610789

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LastDiagMulVec
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_lastDiag_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {r : ℕ}
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have hZi : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hZhi : (Zᴴ)⁻¹ * Zᴴ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)
  rw [Matrix.fromBlocks_mulVec] at hv
  have h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)
  have h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)
  rw [lastDiag_mulVec] at h1 h2
  have h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]
    congr 1
    ring
  have h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]
    congr 1
    ring
  have hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]
  have hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)),
      (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c := by
    intro N c i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  have hyl := congrFun hy (Fin.last r)
  have hxl := congrFun hx (Fin.last r)
  rw [hsingle] at hyl hxl
  rw [hinv] at hxl
  have hprod : (v ∘ Sum.inl) (Fin.last r) *
      (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))))
        = 0 := by
    linear_combination hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl
  have hx0 : (v ∘ Sum.inl) (Fin.last r) = 0 := (mul_eq_zero.mp hprod).resolve_right hG
  have hy0 : (v ∘ Sum.inr) (Fin.last r) = 0 := by rw [hyl, hx0]; ring
  rw [hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hy
  rw [hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hx
  funext s
  cases s with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i
end Formalism.L2.S.L6.UnitaryStandardVectors
