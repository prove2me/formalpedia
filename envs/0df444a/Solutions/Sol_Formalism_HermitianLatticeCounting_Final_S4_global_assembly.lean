-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.global_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:40.767795+00:00
-- url     : https://prove2.me/submissions/4a4db34b-1bdf-4e85-9cae-def50a3beefc

import Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_GaussSumCharacterAverageBound
import Definitions.Def_Formalism_FlagUnipotentLattices_GlobalAssemblyDoubled
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_assembly_numeric_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.WeightedAmplitudeSqSumBoundTwoTypeClasses := Formalism.HermitianLatticeCounting.P.hermitian_assembly_numeric_bound
end Formalism.HermitianLatticeCounting.Final.S4
