-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_norm_of_not_dv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:16:22.18426+00:00
-- url     : https://prove2.me/submissions/d625ed39-2c55-4920-abbf-47e1ca56f7a5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_norm_of_not_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_of_dv_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_norm_representation

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
    (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M) (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V}
    (hy : y ∈ M) (hw : w ∈ M) {a u : K} (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u)
    (hyy : h y y = star a * a * u) (hn : ¬ Dv S π (h w y)) : ∃ X ∈ M, h X X = u := by
  by_cases hau : IsUnitIn S a
  · refine ⟨a⁻¹ • y, hM _ hau.2.2 y hy, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
      hyy]
    have h0 := hau.1
    have h0' : star a ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  have hN := dv_norm_of_not_unit hS hπ ha hau
  by_cases h1 : Dv S π (a * h w y)
  · by_cases h2 : Dv S π (star a * h w y)
    · have hda := dv_of_dv_mul hS hπ (hint w hw y hy) hn h1 h2
      exact exists_norm_representation hS hπ hs hM hint hy hw ha hu huf hyy S.one_mem
        (by rwa [one_mul]) (by rwa [one_mul])
    · exact exists_norm_representation hS hπ hs hM hint hy hw ha hu huf hyy (hS.star_mem _ ha) hN h2
  · exact exists_norm_representation hS hπ hs hM hint hy hw (hS.star_mem _ ha) hu huf
      (by rw [hyy, star_star]; ring) ha (by rwa [mul_comm]) h1
end Formalism.HermitianLattices.Ext.L3.U0
