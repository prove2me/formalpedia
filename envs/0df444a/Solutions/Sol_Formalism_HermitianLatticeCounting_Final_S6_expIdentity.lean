-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.expIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:30.066673+00:00
-- url     : https://prove2.me/submissions/1975765e-91da-477f-8ed7-74c445c207e0

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exponential_identity


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.ExpIdentity := by
  first
    | exact Formalism.HermitianLatticeCounting.P.exponential_identity
    | exact Formalism.HermitianLatticeCounting.P.S6e.exponential_identity
end Formalism.HermitianLatticeCounting.Final.S6
