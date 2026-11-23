-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:29.921807+00:00
-- url     : https://prove2.me/submissions/0d150331-a9d7-483f-addb-cd991583c6e8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_weyl_matrix


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
theorem _root_.solution (m : ℕ) (z D : ℂ) (hz : z ^ (m + 2) = (-1) ^ (m + 3) * D) (v : UT (m + 1 + 1) → ℂ) :
    detM (longM (m + 1 + 1) z v) = (wMat (m + 1)).det * D := by
  have h1 : detM (longM (m + 1 + 1) z v) = (wMat (m + 1 + 1)).det * z ^ (m + 2) :=
    det_orbit.2 (m + 1 + 1) z v
  rw [h1, (det_weyl_matrix (m + 1)).1, hz]
  have h2 : (-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 3) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 2, by ring⟩
  linear_combination ((wMat (m + 1)).det * D) * h2
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
