-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.normSgBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:16.205835+00:00
-- url     : https://prove2.me/submissions/c5dc120b-1ba1-4e39-8d43-bf366a1381e2

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_singular_value_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound
end Formalism.HermitianLatticeCounting.Final.S6
