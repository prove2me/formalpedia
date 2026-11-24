-- Prove2me | solution 1 for Formalism.MainNotions.G.SymmetricFormBlocks.li_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:50.944019+00:00
-- url     : https://prove2.me/submissions/154b1902-ad9d-40e0-be2e-2222eafae692

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiRenameMon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial Finset Formalism.GM.M.SSD
variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)
set_option maxHeartbeats 800000
namespace Formalism.MainNotions.G.SymmetricFormBlocks
theorem _root_.solution {ι : Type} (F : MvPolynomial σ K) (hF : F ≠ 0) (v : ι → MvPolynomial σ K) (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => F * v i) := by
  have hinj : Function.Injective (LinearMap.mulLeft K F) := by
    intro a c h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hF h
  have hfun : (fun i => F * v i) = (LinearMap.mulLeft K F) ∘ v := by
    funext i
    rw [Function.comp_apply, LinearMap.mulLeft_apply]
  rw [hfun]
  exact hv.map' _ (LinearMap.ker_eq_bot.mpr hinj)
end Formalism.MainNotions.G.SymmetricFormBlocks
