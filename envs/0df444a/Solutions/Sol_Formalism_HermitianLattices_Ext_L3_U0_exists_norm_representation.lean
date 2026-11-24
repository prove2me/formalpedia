-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_norm_representation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:41.878937+00:00
-- url     : https://prove2.me/submissions/b69c0517-5cb7-46a4-a17d-d03f98f25c3c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_add
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
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {M : AddSubgroup V} (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V} (hy : y ∈ M) (hw : w ∈ M) {a u ρ₀ : K}
    (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u) (hyy : h y y = star a * a * u)
    (hρ₀ : ρ₀ ∈ S) (h1 : Dv S π (ρ₀ * a)) (h2 : ¬ Dv S π (ρ₀ * h w y)) :
    ∃ X ∈ M, h X X = u := by
  have hσ : ρ₀ * (h w y - u * a) ∈ S :=
    S.mul_mem hρ₀ (S.sub_mem (hint w hw y hy) (S.mul_mem hu.2.1 ha))
  have hσn : ¬ Dv S π (ρ₀ * (h w y - u * a)) := by
    intro hd
    apply h2
    have e : ρ₀ * h w y = ρ₀ * (h w y - u * a) + u * (ρ₀ * a) := by ring
    rw [e]
    exact hd.add (h1.mul_left hu.2.1)
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ hσ hσn
    (S.sub_mem hu.2.1 (hint w hw w hw)) (by rw [star_sub, huf, show star (h w w) = h w w from hs.eq w w])
  have hf := norm_formula hs (ρ := ρ₀ * s) hyy huf (by
    rw [← hs1]
    congr 1
    · ring
    · congr 1; ring)
  have hun : IsUnitIn S (1 + ρ₀ * s * a) := by
    have e : ρ₀ * s * a = ρ₀ * a * s := by ring
    rw [e]
    exact unit_add_dv hπ isUnitIn_one (h1.mul_right hsS)
  refine ⟨(1 + ρ₀ * s * a)⁻¹ • ((ρ₀ * s) • y + w),
    hM _ hun.2.2 _ (M.add_mem (hM _ (S.mul_mem hρ₀ hsS) y hy) hw), ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hf]
  have h0 := hun.1
  have h0' : star (1 + ρ₀ * s * a) ≠ 0 := star_ne_zero.mpr h0
  rw [star_inv₀]
  field_simp
end Formalism.HermitianLattices.Ext.L3.U0
