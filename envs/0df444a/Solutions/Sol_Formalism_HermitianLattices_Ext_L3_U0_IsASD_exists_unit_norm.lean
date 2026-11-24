-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsASD.exists_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:53:17.538886+00:00
-- url     : https://prove2.me/submissions/ad3ce89d-f313-4f92-b3d6-b9a2a04a40b8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_primitive
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_not_inv_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_unit_norm


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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace IsASD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) {z : V} (hM : IsASD S π h W M z) {ξ : V} (hξ : ξ ∈ W)
    (hξ0 : ξ ≠ 0) (hzξ : h z ξ = 0) : ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨l, hl0, hlM, hl⟩ := exists_primitive hS hd hM.toIsLatIn hξ hξ0
  by_cases hex : ∃ w ∈ M, ¬ Dv S π (h w (l • ξ))
  · obtain ⟨w, hw, hn⟩ := hex
    exact Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw hn
  · push_neg at hex
    exfalso
    have hmem : π⁻¹ • (l • ξ) ∈ M := hM.dual _ (W.smul_mem _ (W.smul_mem _ hξ))
      (by rw [map_smul, map_smul, hzξ, smul_zero, smul_zero])
      (fun m hm => by
        rw [map_smul, smul_eq_mul, mul_comm]
        exact hex m hm)
    have h1 := hl (π⁻¹ * l) (by rwa [mul_smul])
    rw [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at h1
    exact not_inv_mem hπ h1
end IsASD
end Formalism.HermitianLattices.Ext.L3.U0
