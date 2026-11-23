-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_coordMap_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:52.640062+00:00
-- url     : https://prove2.me/submissions/cf22d466-d06d-460d-9157-0dbd7873b3ec

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_coord_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_strictUpper_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_entries


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
theorem _root_.solution (n : ℕ) (t c : ℂ) (p : BlockCoord n) : ‖coordMap n t p‖ ≤ ‖orbM n t c p‖ := by
  refine norm_coord_le t (c + p.1 ⬝ᵥ (wMat n *ᵥ (t • p.2.2))) (t • p.2.1) (t • p.2.2)
    (rhoOf t p.1 p.2.1) (orbM n t c p) ?_
  rw [strictUpper_smul]
  exact matrix_entries n t c p
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
