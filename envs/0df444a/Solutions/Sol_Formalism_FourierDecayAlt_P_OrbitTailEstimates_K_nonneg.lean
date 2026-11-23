-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.K_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:22.865664+00:00
-- url     : https://prove2.me/submissions/10c3aeb3-4339-472c-bbde-be791c8d42bd

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
theorem _root_.solution {x y K A : ℝ} (hy : 0 < y) (hx : 0 ≤ x) (h : x ≤ K * min 1 (y ^ (-A))) : 0 ≤ K := by
  have hpos : 0 < min 1 (y ^ (-A)) := lt_min one_pos (Real.rpow_pos_of_pos hy _)
  by_contra hK
  have : K * min 1 (y ^ (-A)) < 0 := mul_neg_of_neg_of_pos (not_le.1 hK) hpos
  linarith
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
