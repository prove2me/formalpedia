-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:13.7744+00:00
-- url     : https://prove2.me/submissions/e08bff65-0097-41cd-a9de-3700fa663559

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_leading_minor_at_block_end


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd := Formalism.HermitianLatticeCounting.P.leading_minor_at_block_end
end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
