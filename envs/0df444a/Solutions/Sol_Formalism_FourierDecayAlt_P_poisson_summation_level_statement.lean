-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_summation_level_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:20.361001+00:00
-- url     : https://prove2.me/submissions/f4ad44ac-2b8b-4dea-a5b2-c633c88fe0dd

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_poissonStep
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_poissonSummable
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_productDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_stepText

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PoissonStepText :=
  PoissonSummationDecay.stepText PoissonSummationDecay.poissonStep PoissonSummationDecay.poissonSummable PoissonSummationDecay.productDecay
end Formalism.FourierDecayAlt.P
