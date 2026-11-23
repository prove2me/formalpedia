-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.continuous_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:08.408339+00:00
-- url     : https://prove2.me/submissions/158186c4-91d1-4b1c-86a6-96460cf60820

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
    Continuous (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      R0 (strictUpper y.2.1) y.2.2 y.1 t) := by
  unfold R0
  refine continuous_finsetSum _ fun j _ => ?_
  refine Continuous.mul (continuous_finsetSum _ fun k _ => ?_) continuous_const
  exact ((continuous_apply k).comp continuous_fst).mul
    ((continuous_apply k.succ).comp ((continuous_powMulVec m j).comp continuous_snd))
end Formalism.FourierDecayAlt.P.G7
