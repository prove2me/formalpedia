-- Prove2me | solution 1 for Formalism.L2.SG.BesselDiscreteSeries.decLow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:36:19.607651+00:00
-- url     : https://prove2.me/submissions/44cd83ed-ab16-49c1-8d28-ce6c5db98244

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_BesselDiscreteSeries_DecLowPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.BesselDiscreteSeries
namespace Formalism.L2.SG.BesselDiscreteSeries
theorem _root_.solution [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] : Formalism.FourierDecayAlt.ThreeDimData.DecLow := Fact.out
end Formalism.L2.SG.BesselDiscreteSeries
