-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.min_le_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:34.422809+00:00
-- url     : https://prove2.me/submissions/356192a8-8564-41ac-be8c-cc6fc9f0cd43

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (A x : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) :
    min 1 (x ^ (-A)) ≤ 2 ^ A * (1 + x) ^ (-A) := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have e : (2 : ℝ) ^ A * (1 + x) ^ (-A) = (2 / (1 + x)) ^ A := by
    rw [Real.rpow_neg h1x.le, Real.div_rpow (by norm_num) h1x.le, div_eq_mul_inv]
  rw [e]
  rcases le_total x 1 with h | h
  · refine (min_le_left _ _).trans (Real.one_le_rpow ?_ hA)
    rw [le_div_iff₀ h1x]; linarith
  · refine (min_le_right _ _).trans ?_
    have hx0 : (0 : ℝ) < x := by linarith
    rw [Real.rpow_neg hx, ← Real.inv_rpow hx]
    refine Real.rpow_le_rpow (by positivity) ?_ hA
    rw [inv_eq_one_div, div_le_div_iff₀ hx0 h1x]; linarith
end Formalism.FourierDecayAlt.P.G7
