-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.colon_count_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:14.47845+00:00
-- url     : https://prove2.me/submissions/64f1ede9-d8a1-49ec-8473-ea20a6cfc950

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_torsion_bound_alt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_count_le_weighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_colon_count_weighted_of_hyp

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
theorem _root_.solution : CCountW := colon_count_weighted_of_hyp ideal_count_le_weighted torsion_bound_alt
end Formalism.HermitianLatticeCounting.P
