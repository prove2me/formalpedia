-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:26.145115+00:00
-- url     : https://prove2.me/submissions/c42de985-eaac-4e33-a60c-4b07bc99fed0

import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Definitions.Def_Formalism_FlagUnipotentLattices_ArithmeticIdentityEntries
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_units_square_index


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.UnitsSquareIndex := Formalism.HermitianLatticeCounting.P.units_square_index
end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
