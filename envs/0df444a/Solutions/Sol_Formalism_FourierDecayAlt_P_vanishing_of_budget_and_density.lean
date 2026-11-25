-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vanishing_of_budget_and_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:29.423152+00:00
-- url     : https://prove2.me/submissions/a4e1927c-5402-4ab2-9396-7b4cf50f67d4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FibreExpansionZeroFails
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingDifferential
import Theorems.Thm_Formalism_FourierDecayAlt_P_big_cell_vanishing_differential
import Theorems.Thm_Formalism_FourierDecayAlt_P_big_cell_threshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_c6_budgetArith_proof
import Theorems.Thm_Formalism_FourierDecayAlt_P_vanishing_of_components_true


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hJ : C6.JCommuteBig) (hB : C6.BudgetClass) (hD : C6.LemmaDens) :
    C6.Vanishing :=
  vanishing_of_components_true (big_cell_vanishing_differential hJ) hB c6_budgetArith_proof big_cell_threshold hD
end Formalism.FourierDecayAlt.P
