-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_jDom_of_nnMaj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:28.38511+00:00
-- url     : https://prove2.me/submissions/95bd76ef-204c-4a1a-a4aa-f4f791e7926d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_jDomBound_of_nnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_jDom_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_bessel_domain_measurable


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
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs2.jDom_of_parts Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable (Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj h)
end Formalism.FourierDecayAlt.P
