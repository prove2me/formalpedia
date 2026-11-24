-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:39.41212+00:00
-- url     : https://prove2.me/submissions/e19099ff-d3af-4960-b185-1e5a6742fbb7

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by
  intro K V _ _ _ _ H r F F' hA y hy hyo
  exact hA y hyo ((X_iso F') hy hy)
end Formalism.HermitianLatticeCounting.P
