-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.class_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:01:36.783612+00:00
-- url     : https://prove2.me/submissions/bc0eee05-e6a1-464d-aa7f-9ba313555b0b

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_t_ClassCS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.PN.ClassCS := HermitianFormNormLemmas.C.t_ClassCS
end Formalism.FourierDecayAlt.P
