-- Prove2me | solution 1 for Formalism.L2.Th1.H.unitary_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:12.023971+00:00
-- url     : https://prove2.me/submissions/558eec80-0e5b-4c71-b5f7-d69a61a54c22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Theorems.Thm_Formalism_L2_Th1_H_relIndex_map_real
import Theorems.Thm_Formalism_L2_Th1_H_exists_basis_of_lattice
import Theorems.Thm_Formalism_L2_Th1_H_isLat_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : UnitaryIndex := by
  intro V _ _ _ H Λ α δ Ae hL hU
  have hle : latA Λ δ Ae ≤ Λ := by
    rintro y ⟨x, ⟨hxΛ, ⟨z, hz, rfl⟩⟩, rfl⟩
    show Ae (δ z) ∈ Λ
    rw [hU.cay, LinearEquiv.symm_apply_apply]
    exact Λ.sub_mem hxΛ hz
  refine ⟨hle, ?_⟩
  obtain ⟨b₂, hb₂⟩ := exists_basis_of_lattice Λ hL.1 hL.2
  have hL1 := isLat_inf hL hU.idx₁
  obtain ⟨b₁, hb₁⟩ := exists_basis_of_lattice (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) hL1.1 hL1.2
  let f : V ≃ₗ[ℝ] V := Ae.restrictScalars ℝ
  have hmap : latA Λ δ Ae
      = (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ).map (f : V →ₗ[ℝ] V).toAddMonoidHom := rfl
  have key := relIndex_map_real (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) Λ inf_le_left b₁ b₂ hb₁ hb₂ f
    (by rw [← hmap]; exact hle)
  unfold relIdx
  rw [hmap, key, AddSubgroup.inf_relIndex_left]
  congr 1
  have hd : LinearMap.det (f : V →ₗ[ℝ] V)
      = Algebra.norm ℝ (LinearMap.det (Ae : V →ₗ[ℂ] V)) := LinearMap.det_restrictScalars
  rw [hd, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  exact abs_of_nonneg (by positivity)
end Formalism.L2.Th1.H
