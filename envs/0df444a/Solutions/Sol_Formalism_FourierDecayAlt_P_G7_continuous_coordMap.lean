-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.continuous_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:22.241858+00:00
-- url     : https://prove2.me/submissions/10f6209e-26f6-405a-8675-702d1e711b7c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_upper

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
theorem _root_.solution (n : ℕ) (t : ℂ) : Continuous (coordMap n t) := by
  unfold coordMap rhoOf
  refine Continuous.prodMk ?_ (by fun_prop)
  exact (Continuous.matrix_vecMul continuous_fst
    (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_snd)))).const_smul t
end Formalism.FourierDecayAlt.P.G7
