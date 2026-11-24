-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.ExpansionTerms.majorant_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:30.732383+00:00
-- url     : https://prove2.me/submissions/cd284c5e-3fb2-440b-951a-19077f88ca84

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_last_distance_lower_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.Final.ExpansionTerms
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := Formalism.HermitianLatticeCounting.P.last_distance_lower_bound
end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
