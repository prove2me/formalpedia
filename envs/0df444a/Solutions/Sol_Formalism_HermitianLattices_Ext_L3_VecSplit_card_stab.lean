-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.card_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:57.136733+00:00
-- url     : https://prove2.me/submissions/74f647f6-2ec8-4392-bf22-0b76e45843f5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_autL_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_gmap_extOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_gmap_res
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_spec
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open SplitBAux
namespace Formalism.HermitianLattices.Ext.L3
namespace VecSplit
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : S.adjoin (S.cut L) = L) :
    Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g S.x₀ = S.x₀} =
      Nat.card (Formalism.ThetaLiftIndependence.autL h' (S.cut L)) := by
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨res S g.1 (autL_iff.mp g.2.1).1 g.2.2,
        autL_iff.mpr ⟨res_mem_isom S _ _ _, gmap_res S _ _ _ (autL_iff.mp g.2.1).2⟩⟩
      invFun := fun g' => ⟨extOf S g'.1,
        autL_iff.mpr ⟨extOf_mem_isom hs S (autL_iff.mp g'.2).1, by
          have := gmap_extOf S g'.1 (autL_iff.mp g'.2).2
          rwa [hL] at this⟩, extOf_x₀ S _⟩
      left_inv := fun g => Subtype.ext (LinearEquiv.toLinearMap_injective
        (linearMap_ext S (by simp [extOf_x₀, g.2.2]) (fun a => by simp [extOf_ι, res_spec])))
      right_inv := fun g' => Subtype.ext (LinearEquiv.ext fun a => S.inj (by
        simp [res_spec, extOf_ι])) }
end VecSplit
end Formalism.HermitianLattices.Ext.L3
