-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.ExpansionTerms.mass_inequality_iteration
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:11.615105+00:00
-- url     : https://prove2.me/submissions/8b7da682-40b4-4735-8634-4b5eba8cfbe1

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_moment_recursion_iterate


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentRecursionIterate := Formalism.HermitianLatticeCounting.P.moment_recursion_iterate
end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
