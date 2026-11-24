-- Prove2me | solution 1 for Formalism.REAL.arr_operator_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:10.922923+00:00
-- url     : https://prove2.me/submissions/d827e51a-dd21-4491-a21c-6a5bd8e7940c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_fin_one_update_eq_const
import Theorems.Thm_Formalism_REAL_factorAction_apply_general
import Theorems.Thm_Formalism_REAL_pointwise_operator_apply_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n 1)
    (a b : Fin n) :
    arrE E 1 c d F (fun _ => (a, b)) =
      ((if a = c then F (fun _ => (d, b)) else 0) - (if b = d then F (fun _ => (a, c)) else 0))
        + E c d (F (fun _ => (a, b))) := by
  simp only [arrE, LinearMap.add_apply, Fin.sum_univ_one, PiLp.add_apply, factorAction_apply_general,
    pointwise_operator_apply_general, fin_one_update_eq_const]
end Formalism.REAL
