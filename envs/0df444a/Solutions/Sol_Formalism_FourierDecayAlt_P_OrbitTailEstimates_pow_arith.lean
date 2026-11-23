-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.pow_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:17.655738+00:00
-- url     : https://prove2.me/submissions/1d890f55-2ad1-4d58-9952-4c1807ccaf61

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (m : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ ((m + 1) ^ 2) * ((x ^ ((m + 1) * (m + 4)))⁻¹ * x ^ (3 * m + 4)) = x := by
  have e : x ^ ((m + 1) ^ 2) * x ^ (3 * m + 4) = x ^ ((m + 1) * (m + 4)) * x := by
    rw [← pow_add, ← pow_succ]; congr 1; ring
  have h0 : x ^ ((m + 1) * (m + 4)) ≠ 0 := (pow_pos hx _).ne'
  calc x ^ ((m + 1) ^ 2) * ((x ^ ((m + 1) * (m + 4)))⁻¹ * x ^ (3 * m + 4))
      = (x ^ ((m + 1) * (m + 4)))⁻¹ * (x ^ ((m + 1) ^ 2) * x ^ (3 * m + 4)) := by ring
    _ = x := by rw [e, inv_mul_cancel_left₀ h0]
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
