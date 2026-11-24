-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:57:46.465441+00:00
-- url     : https://prove2.me/submissions/4c0f3adc-f8a1-4977-9fb8-ebc60b3c64a9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_left
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_add_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_of_not_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_trace_mul

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
    (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V} (hy : y ∈ M) (hw : w ∈ M)
    (hn : ¬ Dv S π (h w y)) : ∃ x ∈ M, IsUnitIn S (h x x) := by
  by_cases h1 : IsUnitIn S (h y y)
  · exact ⟨y, hy, h1⟩
  by_cases h2 : IsUnitIn S (h w w)
  · exact ⟨w, hw, h2⟩
  have d1 := dv_of_not_unit hπ (hint y hy y hy) (hs.eq y y) h1
  have d2 := dv_of_not_unit hπ (hint w hw w hw) (hs.eq w w) h2
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ (hint w hw y hy) hn S.one_mem (star_one K)
  refine ⟨s • y + w, M.add_mem (hM s hsS y hy) hw, ?_⟩
  have hyw : h y w = star (h w y) := (hs.eq w y).symm
  have e : h (s • y + w) (s • y + w) = 1 + (star s * s * h y y + h w w) := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hyw,
      starRingEnd_apply, RingHom.id_apply]
    simp only [star_mul'] at hs1
    linear_combination hs1
  rw [e]
  exact unit_add_dv hπ isUnitIn_one
    ((d1.mul_left (S.mul_mem (hS.star_mem _ hsS) hsS)).add d2)
end Formalism.HermitianLattices.Ext.L3.U0
