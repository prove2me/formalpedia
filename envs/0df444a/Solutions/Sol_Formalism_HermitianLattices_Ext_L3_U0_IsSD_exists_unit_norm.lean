-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsSD.exists_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:15.700202+00:00
-- url     : https://prove2.me/submissions/b232bb77-d4e3-44ce-bde3-2cbad4a34007

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_primitive
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_not_dv
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
namespace IsSD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨l, hl0, hlM, hl⟩ := exists_primitive hS hd hM.toIsLatIn hξ hξ0
  have hprim : ∀ c : K, c • (l • ξ) ∈ M → c ∈ S := fun c hc => by
    have h1 := hl (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at h1
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hlM hprim
  exact Formalism.HermitianLattices.Ext.L3.U0.exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw hn
end IsSD
end Formalism.HermitianLattices.Ext.L3.U0
