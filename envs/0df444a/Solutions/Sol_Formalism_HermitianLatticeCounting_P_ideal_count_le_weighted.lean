-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:58.853901+00:00
-- url     : https://prove2.me/submissions/aea925ce-e354-431e-8c1e-4db0b5ec19c9

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_count_le_weighted_of_hyp
import Theorems.Thm_Formalism_SLP_Final_omegaPow
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
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IdealCountLeW :=
  ideal_count_le_weighted_of_hyp Formalism.SLP.Final.submoduleIndexCountO Formalism.SLP.Final.omegaPow
end Formalism.HermitianLatticeCounting.P
