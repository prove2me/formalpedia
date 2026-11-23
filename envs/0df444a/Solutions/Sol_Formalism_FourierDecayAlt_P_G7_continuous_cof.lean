-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.continuous_cof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:08.141647+00:00
-- url     : https://prove2.me/submissions/8bec9a8d-9590-4830-b073-1fb577e57ff3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_powMulVec

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
theorem _root_.solution (m : ℕ) (t : ℂ) :
    Continuous (fun z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) => Cof (strictUpper z.1) z.2 t) := by
  unfold Cof
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply 0).comp (continuous_powMulVec m j)).mul continuous_const
end Formalism.FourierDecayAlt.P.G7
