-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_jWords_of_nnMaj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:50.23883+00:00
-- url     : https://prove2.me/submissions/70d87cc9-8095-4b61-b18d-622ecad16db1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_jDom_of_nnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_words_of_domain


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
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JWords := fun h =>
  Formalism.FourierDecayAlt.P.bessel_words_of_domain (jf_jDom_of_nnMaj h)
end Formalism.FourierDecayAlt.P
