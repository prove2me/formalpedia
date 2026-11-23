-- Prove2me | solution 1 for Formalism.REAL.deriv_mulX_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:10.208013+00:00
-- url     : https://prove2.me/submissions/105ef9a2-434e-4e49-ba30-e1f1ce799b60

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
theorem _root_.solution (v w : σ) : (D v) * (Mx w) - (Mx w) * (D v) = if v = w then 1 else 0 := by
  by_cases h : v = w
  · subst h
    refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply]
    all_goals abel
  · refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply, h, Ne.symm h]
end Formalism.REAL
