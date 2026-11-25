-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.IA.surjective_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:58:24.871681+00:00
-- url     : https://prove2.me/submissions/bf02a807-8f41-4f5f-8d90-1fb8409ca390

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2 Formalism.HermitianLattices.Ext.L3.D2.IA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace Formalism.HermitianLattices.Ext.L3.D2.IA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop
end Formalism.HermitianLattices.Ext.L3.D2.IA
