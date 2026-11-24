-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.minkowskiDvdFactorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:13.444785+00:00
-- url     : https://prove2.me/submissions/ded74f54-4fb7-4299-be06-333e5070e20b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minkowski_number_dvd_factorial


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.MinkowskiDvdFactorial := by
  first
    | exact Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial
    | exact Formalism.HermitianLatticeCounting.P.S6e.minkowski_number_dvd_factorial
end Formalism.HermitianLatticeCounting.Final.S6
