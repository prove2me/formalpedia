-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.amplitude_continuous_at_critical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:24.240956+00:00
-- url     : https://prove2.me/submissions/4609dab2-0411-490f-be16-fb6fddee9359

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_ampCrit_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_cofactor_lower_bound_radius
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_matrix_xy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.AmpCritContinuous :=
  PhaseFunctionDerivatives.d_ampCrit_of cofactor_lower_bound_radius det_matrix_xy
end Formalism.FourierDecayAlt.P
