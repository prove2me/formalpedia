-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.coordinate_sizes_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:40:38.915533+00:00
-- url     : https://prove2.me/submissions/7adeb63a-4415-476b-80bc-f17b15c908ec

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_coordinate_sizes_of_parts_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.CoordinateSizesFromComponents := Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_parts_holds
end Formalism.FourierDecayAlt.P
