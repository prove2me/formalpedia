-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.submodule_generator_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.426457+00:00
-- url     : https://prove2.me/submissions/001c1a3b-762a-4683-85e6-e59102975c7b

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_SLP_P_exists_family_span_eq_of_le


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
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SubGen := by
  intro R Q _ _ _ _ _ e s hs N
  exact Formalism.SLP.P.exists_family_span_eq_of_le e s N (by rw [hs]; exact le_top)
end Formalism.HermitianLatticeCounting.P
