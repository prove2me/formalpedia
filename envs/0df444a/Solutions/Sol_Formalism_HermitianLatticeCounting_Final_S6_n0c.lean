-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.n0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:01:02.80658+00:00
-- url     : https://prove2.me/submissions/12bf8a1c-eea7-4bed-9e9b-d6afac4e948b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_memOfOrthogonalAnisotropic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S6
namespace Formalism.HermitianLatticeCounting.Final.S6
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by
  first
    | exact Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic
    | exact Formalism.HermitianLatticeCounting.P.S6e.memOfOrthogonalAnisotropic
end Formalism.HermitianLatticeCounting.Final.S6
