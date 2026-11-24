-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_norm_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:40.845801+00:00
-- url     : https://prove2.me/submissions/932aaac6-d02c-4782-ad01-5f241e89ef4b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_inv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_left
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_right
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_add_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_trace_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_norm_formula

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
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
variable {V : Type*} [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M) {y w : V}
    (hy : y ∈ M) (hw : w ∈ M) {a u : K} (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u)
    (hyy : h y y = star a * a * u) (hna : ¬ Dv S π a) (hN : Dv S π (star a * a))
    (hwy : h w y = 0) (hww : IsUnitIn S (h w w)) : ∃ X ∈ M, h X X = u := by
  have hσn : ¬ Dv S π (-(u * a)) := by
    intro hd
    apply hna
    have e : a = -(u * a) * (-u⁻¹) := by
      have := hu.1
      field_simp
    rw [e]
    exact hd.mul_right (S.neg_mem hu.2.2)
  obtain ⟨ρ, hρS, hρ⟩ := exists_trace_mul hS hπ (S.neg_mem (S.mul_mem hu.2.1 ha)) hσn
    (S.sub_mem hu.2.1 hww.2.1) (by rw [star_sub, huf, show star (h w w) = h w w from hs.eq w w])
  have hf := norm_formula hs (ρ := ρ) hyy huf (by
    rw [← hρ, hwy, zero_sub, mul_comm])
  have hNu : IsUnitIn S (star (1 + ρ * a) * (1 + ρ * a)) := by
    have e : star (1 + ρ * a) * (1 + ρ * a) = h w w * u⁻¹ + star ρ * ρ * (star a * a) := by
      have h0 := hu.1
      have e2 : u * (star (1 + ρ * a) * (1 + ρ * a)) =
          u * (h w w * u⁻¹ + star ρ * ρ * (star a * a)) := by
        have e3 : u * (h w w * u⁻¹) = h w w := by field_simp
        rw [mul_add u (h w w * u⁻¹), e3]
        simp only [star_mul', star_neg, huf, star_add, star_one] at hρ ⊢
        linear_combination -hρ
      exact mul_left_cancel₀ h0 e2
    rw [e]
    exact unit_add_dv hπ (unit_mul hww (unit_inv hu))
      (hN.mul_left (S.mul_mem (hS.star_mem _ hρS) hρS))
  have h1S : 1 + ρ * a ∈ S := S.add_mem S.one_mem (S.mul_mem hρS ha)
  have hun := isUnitIn_of_mul (hS.star_mem _ h1S) h1S hNu
  refine ⟨(1 + ρ * a)⁻¹ • (ρ • y + w), hM _ hun.2.2 _ (M.add_mem (hM _ hρS y hy) hw), ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hf]
  have h0 := hun.1
  have h0' : star (1 + ρ * a) ≠ 0 := star_ne_zero.mpr h0
  rw [star_inv₀]
  field_simp
end Formalism.HermitianLattices.Ext.L3.U0
