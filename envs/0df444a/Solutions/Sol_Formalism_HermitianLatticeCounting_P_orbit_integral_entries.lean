-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.orbit_integral_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:14.684574+00:00
-- url     : https://prove2.me/submissions/92e68995-7ad2-46fb-8984-1ebd4dffa89b

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_leading_minor_at_block_end
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_orbit_integral_entries_of_leading_minor_at_block_end

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := orbit_integral_entries_of_leading_minor_at_block_end leading_minor_at_block_end
end Formalism.HermitianLatticeCounting.P
