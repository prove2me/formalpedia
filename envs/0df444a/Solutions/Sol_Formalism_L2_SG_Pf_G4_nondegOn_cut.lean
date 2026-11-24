-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G4.nondegOn_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:35.335651+00:00
-- url     : https://prove2.me/submissions/8de79c06-79d0-459a-acc2-9276355edece

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G4
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.L2.SG.Pf.G4
theorem _root_.solution (hnd : NondegOn h W) {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    NondegOn h (cutW h W x) := by
  intro ξ hξ hξ0
  rw [mem_cutW] at hξ
  obtain ⟨w, hw, hwξ⟩ := hnd ξ hξ.1 hξ0
  refine ⟨w - (h x w * (h x x)⁻¹) • x, ?_, ?_⟩
  · rw [mem_cutW]
    refine ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hxx, sub_self]
  · rw [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, hξ.2, smul_zero, sub_zero]
    exact hwξ
end Formalism.L2.SG.Pf.G4
