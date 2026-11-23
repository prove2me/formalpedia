-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.smooth_cutoff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:14.52848+00:00
-- url     : https://prove2.me/submissions/dac57be2-ff32-49e8-a53a-482cd96aeb35

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution (r : ℝ) : chi0 r ≤ 1 := Real.smoothTransition.le_one _
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
