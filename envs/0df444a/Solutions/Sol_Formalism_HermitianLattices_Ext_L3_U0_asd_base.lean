-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.asd_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:36.448022+00:00
-- url     : https://prove2.me/submissions/b1c2bb0e-32b4-4e6f-935c-95a7bd36753f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_mem_iff_of_line
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_z_norm_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isom_scale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_inv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    {W₁ W₂ : Submodule K V} {M N : AddSubgroup V} {z₁ z₂ : V} {φ : V ≃ₗ[K] V}
    (hM : IsASD S π h W₁ M z₁) (hN : IsASD S π h W₂ N z₂) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) (h1 : ¬ ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0)
    (h2 : ¬ ∃ ξ ∈ W₂, ξ ≠ 0 ∧ h z₂ ξ = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
  obtain ⟨-, hMl⟩ := hM.mem_iff_of_line hπ h1
  obtain ⟨hW₂l, hNl⟩ := hN.mem_iff_of_line hπ h2
  have hζ₂ := hN.z_norm_ne
  obtain ⟨l, hl⟩ : ∃ l : K, φ z₁ = l • z₂ := ⟨_, hW₂l _ ((hW z₁).mp (hM.le _ hM.z_mem))⟩
  have hnorm : h z₁ z₁ = star l * l * h z₂ z₂ := by
    rw [← hφ', hl]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  have hNl' : IsUnitIn S (star l * l) := by
    have e : star l * l = h z₁ z₁ * π⁻¹ * (h z₂ z₂ * π⁻¹)⁻¹ := by
      rw [hnorm]
      have := hπ.ne
      field_simp
    rw [e]
    exact unit_mul hM.z_norm (unit_inv hN.z_norm)
  obtain ⟨b, hb, hlb⟩ := exists_norm_one_mul_mem hS hNl'.2.1
  have hlbu : IsUnitIn S (l * b) := by
    apply isUnitIn_of_mul (hS.star_mem _ hlb) hlb
    have e : star (l * b) * (l * b) = star l * l := by
      rw [star_mul']
      linear_combination (star l * l) * hb
    rw [e]
    exact hNl'
  obtain ⟨ψ, hψ, hψz, hψfix⟩ := exists_isom_scale hs hζ₂ hb
  have hgz : ψ (φ z₁) = (l * b) • z₂ := by rw [hl, map_smul, hψz, smul_smul]
  refine ⟨ψ * φ, mul_mem hψ hφ, fun v hv => ?_, fun v => ?_⟩
  · change ψ (φ v) = φ v
    apply hψfix
    have h3 : φ.symm z₂ ∈ W₁ := by rw [hW, φ.apply_symm_apply]; exact hN.le _ hN.z_mem
    have := hv _ h3
    rwa [← hφ', φ.apply_symm_apply] at this
  · change v ∈ M ↔ ψ (φ v) ∈ N
    rw [hMl, hNl]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c * (l * b), S.mul_mem hc hlb, by rw [map_smul, map_smul, hgz, smul_smul]⟩
    · rintro ⟨c, hc, hv⟩
      refine ⟨c * (l * b)⁻¹, S.mul_mem hc hlbu.2.2, ?_⟩
      apply φ.injective
      apply ψ.injective
      rw [hv, map_smul, map_smul, hgz, smul_smul, mul_assoc, inv_mul_cancel₀ hlbu.1, mul_one]
end Formalism.HermitianLattices.Ext.L3.U0
