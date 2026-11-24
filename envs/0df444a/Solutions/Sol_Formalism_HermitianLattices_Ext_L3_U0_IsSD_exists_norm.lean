-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsSD.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:46.831678+00:00
-- url     : https://prove2.me/submissions/648b49cb-9dd0-452d-8d64-fde629666536

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_primitive_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_not_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_norm_of_not_dv

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
namespace IsSD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, _, ⟨l, rfl⟩, hprim, a, ha, hyy⟩ :=
    exists_primitive_norm hS hd hM.toIsLatIn hξ hu hξu
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hy hprim
  have huf : star u = u := by rw [← hξu]; exact star_apply_eq_apply_swap_of_isSymm' hs ξ ξ
  exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn
end IsSD
end Formalism.HermitianLattices.Ext.L3.U0
