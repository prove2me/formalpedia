-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sublattice_count_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:00.333266+00:00
-- url     : https://prove2.me/submissions/1dba6f09-6138-455c-ba68-e39b5d27cb54

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_coefficient_field_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sublatticeCount_of
import Theorems.Thm_Formalism_SLP_Final_submoduleIndexCountO


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.SublatticeCount :=
  sublatticeCount_of Formalism.SLP.Final.submoduleIndexCountO coefficient_field_bound
end Formalism.HermitianLatticeCounting.P
