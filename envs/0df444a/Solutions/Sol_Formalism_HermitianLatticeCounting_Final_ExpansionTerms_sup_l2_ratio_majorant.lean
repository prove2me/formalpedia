-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.ExpansionTerms.sup_l2_ratio_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:01.002911+00:00
-- url     : https://prove2.me/submissions/4e6a5daf-6938-4e1d-a371-21764b8e5363

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_first_operator_norm_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.supL2RatioMajorant := Formalism.HermitianLatticeCounting.P.first_operator_norm_bound
end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
