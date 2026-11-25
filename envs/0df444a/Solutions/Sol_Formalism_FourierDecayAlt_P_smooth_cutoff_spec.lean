-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.smooth_cutoff_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:51:20.274061+00:00
-- url     : https://prove2.me/submissions/3926f3ba-5d96-4b26-8e95-f24e122b541d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.Chi0Spec := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r => ⟨?_, ?_⟩, fun k => ?_⟩
  · exact Real.smoothTransition.one_of_one_le (by linarith)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.nonneg _
  · exact Real.smoothTransition.le_one _
  · exact (Real.smoothTransition.contDiff).comp (contDiff_const.sub contDiff_id)
end Formalism.FourierDecayAlt.P
