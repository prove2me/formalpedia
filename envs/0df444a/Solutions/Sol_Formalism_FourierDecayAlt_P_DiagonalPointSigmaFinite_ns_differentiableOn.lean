-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:09.509523+00:00
-- url     : https://prove2.me/submissions/4e295c9a-b0b2-4974-9bf2-fc8656099f73

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (m : ℕ) (D' : ℂ) {r d : ℝ} (hr : 0 ≤ r) :
    DifferentiableOn ℂ (g0 D') (ns_Om m D' r d) := by
  intro x hx
  have hne : ∏ k, x k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => by
    have := hr.trans_lt (hx.1 k)
    exact norm_pos_iff.mp this
  apply DifferentiableAt.differentiableWithinAt
  have hp : DifferentiableAt ℂ (fun x : Fin (m + 1) → ℂ => ∏ k, x k) x := by fun_prop
  have hs : DifferentiableAt ℂ (fun x : Fin (m + 1) → ℂ => ∑ k, x k) x := by fun_prop
  have hd : DifferentiableAt ℂ (fun x : Fin (m + 1) → ℂ => D' / ∏ k, x k) x := by
    simp only [div_eq_mul_inv]
    exact (hp.fun_inv hne).const_mul D'
  exact hs.fun_add hd
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
