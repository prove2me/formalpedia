-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsASD.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:45.525733+00:00
-- url     : https://prove2.me/submissions/74de4894-9433-415d-b187-0415fd59f646

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_z_norm_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mul_inv_mem_of_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
private theorem star_apply_eq_apply_swap_of_isSymm' (hs : h.IsSymm) (x y : V) : star (h x y) = h y x := by
  have h1 := hs.eq x y
  rwa [starRingEnd_apply] at h1
end Formalism.HermitianLattices.Ext.L3.U0
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace IsASD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {z : V}
    (hM : IsASD S π h W M z) {y : V} (hy : y ∈ M) (hall : ∀ w ∈ M, Dv S π (h w y)) :
    ∃ n₀ ∈ M, ∃ t ∈ S, h z n₀ = 0 ∧ y = π • n₀ + t • z := by
  have hzz : h z z ≠ 0 := hM.z_norm_ne
  have htS : h z y * (h z z)⁻¹ ∈ S := mul_inv_mem_of_dv hπ (hall z hM.z_mem) hM.z_norm
  have hzn : h z (π⁻¹ • (y - (h z y * (h z z)⁻¹) • z)) = 0 := by
    simp only [map_smul, map_sub, smul_eq_mul]
    rw [mul_assoc (h z y), inv_mul_cancel₀ hzz, mul_one, sub_self, mul_zero]
  refine ⟨π⁻¹ • (y - (h z y * (h z z)⁻¹) • z), ?_, h z y * (h z z)⁻¹, htS, hzn, ?_⟩
  · refine hM.dual _ (W.smul_mem _ (W.sub_mem (hM.le y hy) (W.smul_mem _ (hM.le z hM.z_mem))))
      hzn ?_
    intro m hm
    have h1 : h m y * π⁻¹ ∈ S := hall m hm
    have h2 : h m z * π⁻¹ ∈ S := by
      have h3 := Dv.star hS hπ (hM.z_rad m hm)
      rw [star_apply_eq_apply_swap_of_isSymm' hs] at h3
      exact h3
    have e : h m (π⁻¹ • (y - (h z y * (h z z)⁻¹) • z)) =
        h m y * π⁻¹ - (h z y * (h z z)⁻¹) * (h m z * π⁻¹) := by
      simp only [map_smul, map_sub, smul_eq_mul]
      ring
    rw [e]
    exact S.sub_mem h1 (S.mul_mem htS h2)
  · rw [smul_smul, mul_inv_cancel₀ hπ.ne, one_smul, sub_add_cancel]
end IsASD
end Formalism.HermitianLattices.Ext.L3.U0
