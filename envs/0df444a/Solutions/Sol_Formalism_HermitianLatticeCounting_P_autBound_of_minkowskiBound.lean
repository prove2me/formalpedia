-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.autBound_of_minkowskiBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:01.5644+00:00
-- url     : https://prove2.me/submissions/4c3b5e47-296f-423f-9a23-e09e213d7875

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minkowski_number_dvd_factorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_automorphism_bound_of_hyp

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
theorem _root_.solution (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) : Formalism.HermitianLatticeCounting.S6.AutBound :=
  automorphism_bound_of_hyp hM minkowski_number_dvd_factorial
end Formalism.HermitianLatticeCounting.P
