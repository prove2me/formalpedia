-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.global_assembly_doubled
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:12.651805+00:00
-- url     : https://prove2.me/submissions/c3e486bb-9567-44ff-b266-2f8ec8d142df

import Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_GaussSumCharacterAverageBound
import Definitions.Def_Formalism_FlagUnipotentLattices_GlobalAssemblyDoubled
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_non_generic_bound_large_height


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4
namespace Formalism.HermitianLatticeCounting.Final.S4
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.NonGenericBoundLargeHeight := Formalism.HermitianLatticeCounting.P.non_generic_bound_large_height
end Formalism.HermitianLatticeCounting.Final.S4
