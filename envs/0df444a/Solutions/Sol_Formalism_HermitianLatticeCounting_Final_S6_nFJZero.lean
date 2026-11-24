-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.nFJZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:24.869483+00:00
-- url     : https://prove2.me/submissions/dd1e80e8-9090-4ca9-a9bc-da6720f77430

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normalFormZero


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero
end Formalism.HermitianLatticeCounting.Final.S6
