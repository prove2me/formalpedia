-- Prove2me | solution 1 for Formalism.FG.functional_equation_hom_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:45.27725+00:00
-- url     : https://prove2.me/submissions/2b8df345-32d9-4a59-ba75-72f2867b7dec

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Theorems.Thm_Formalism_FG_FunEqHomV_of
import Theorems.Thm_Formalism_FG_functional_equation_subst_vector
import Theorems.Thm_Formalism_FG_inverse_integral_vector
import Theorems.Thm_Formalism_FG_low_coeff_vector
import Theorems.Thm_Formalism_FG_solve_exists_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.FunEqHomV.{u, v, w} :=
  FunEqHomV_of solve_exists_vector inverse_integral_vector low_coeff_vector functional_equation_subst_vector
end Formalism.FG
