-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_jqSmooth_of_nnMaj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:14.112024+00:00
-- url     : https://prove2.me/submissions/99cb4d2c-598b-44a7-b275-7a1d78832bde

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_jDom_of_nnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_CellSmoothness_jqSmooth_of_jDom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JqSmooth := fun h =>
  Formalism.FourierDecayAlt.P.CellSmoothness.jqSmooth_of_jDom (jf_jDom_of_nnMaj h)
end Formalism.FourierDecayAlt.P
