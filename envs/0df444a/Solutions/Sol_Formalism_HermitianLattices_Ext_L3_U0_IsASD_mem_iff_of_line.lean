-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsASD.mem_iff_of_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:45.693621+00:00
-- url     : https://prove2.me/submissions/967d3568-fa4c-4fa1-a1eb-45751986b4e7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_z_norm_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mul_inv_mem_of_dv


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
namespace IsASD
theorem _root_.solution (hπ : IsUnif S π) {W : Submodule K V} {M : AddSubgroup V} {z : V}
    (hM : IsASD S π h W M z) (hline : ¬ ∃ ξ ∈ W, ξ ≠ 0 ∧ h z ξ = 0) :
    (∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z) ∧ ∀ v, v ∈ M ↔ ∃ c ∈ S, v = c • z := by
  have hζ := hM.z_norm_ne
  have h1 : ∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z := by
    intro v hv
    by_contra hne
    apply hline
    refine ⟨v - (h z v * (h z z)⁻¹) • z, W.sub_mem hv (W.smul_mem _ (hM.le z hM.z_mem)),
      sub_ne_zero.mpr hne, ?_⟩
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  refine ⟨h1, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact ⟨_, mul_inv_mem_of_dv hπ (hM.z_rad v hv) hM.z_norm, h1 v (hM.le v hv)⟩
  · rintro ⟨c, hc, rfl⟩
    exact hM.smul_mem c hc z hM.z_mem
end IsASD
end Formalism.HermitianLattices.Ext.L3.U0
