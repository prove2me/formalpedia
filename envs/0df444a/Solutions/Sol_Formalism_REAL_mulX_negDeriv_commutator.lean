-- Prove2me | solution 1 for Formalism.REAL.mulX_negDeriv_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:01.564814+00:00
-- url     : https://prove2.me/submissions/b8d510af-527d-433b-88d7-9c72b87e2572

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {σ : Type*} [DecidableEq σ]
set_option quotPrecheck false
local notation "D" v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap :
  Module.End ℂ (MvPolynomial σ ℂ))
local notation "Mx" v => (LinearMap.mulLeft ℂ (X v : MvPolynomial σ ℂ) : Module.End ℂ (MvPolynomial σ ℂ))
namespace Formalism.REAL
theorem _root_.solution (v w : σ) : (Mx v) * -(D w) - -(D w) * (Mx v) = if v = w then 1 else 0 := by
  by_cases h : v = w
  · subst h
    refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply]
    all_goals abel
  · refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply, h, Ne.symm h]
    all_goals abel
end Formalism.REAL
