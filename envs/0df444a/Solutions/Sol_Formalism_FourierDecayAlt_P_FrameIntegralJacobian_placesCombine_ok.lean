-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.placesCombine_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:50.667487+00:00
-- url     : https://prove2.me/submissions/9c795efc-2d1b-4fdd-9401-124a4759cc71

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
theorem _root_.solution : PlacesCombine := by
  unfold PlacesCombine
  intro ι _ _ K abelian₂ o N S hL hS h
  have hpos : 0 < ∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K := by
    apply Finset.prod_pos
    intro v hv
    have hv' : abelian₂ v < o v := (Finset.mem_filter.mp hv).2
    exact pow_pos (lt_of_le_of_lt (hL v) hv') K
  have hprod : ∏ v, minFac (abelian₂ v) (o v) K =
      (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), abelian₂ v ^ K) /
        (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K) := by
    simp only [minFac, div_pow]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib]
  rw [hprod, div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm N]
  exact h
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
