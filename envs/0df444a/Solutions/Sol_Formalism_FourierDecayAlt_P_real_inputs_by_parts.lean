-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.real_inputs_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:04.896904+00:00
-- url     : https://prove2.me/submissions/4354e0d0-899d-427c-92b6-3e01df6a97d6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConcreteBoundOfRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.RealInputsConcreteOfParts := by
  intro hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  exact ⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e,
    hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e,
    hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e,
    hCut E Wp Wq S H Vt hPG Kr hK0 Th e⟩
end Formalism.FourierDecayAlt.P
