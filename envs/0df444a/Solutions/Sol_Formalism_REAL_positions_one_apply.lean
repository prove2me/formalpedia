-- Prove2me | solution 1 for Formalism.REAL.positions_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:55.700565+00:00
-- url     : https://prove2.me/submissions/fdef9a3a-491e-4009-9cd6-13a5e9f74eee

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_fin_one_update_eq_const
import Theorems.Thm_Formalism_REAL_factorAction_apply_general

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
theorem _root_.solution (c d : Fin n) (G : Arr V n 1) (a b : Fin n) :
    positionsE V n 1 c d G (fun _ => (a, b)) =
      (if a = c then G (fun _ => (d, b)) else 0) - (if b = d then G (fun _ => (a, c)) else 0) := by
  simp only [positionsE, Fin.sum_univ_one, factorAction_apply_general,
    fin_one_update_eq_const]
end Formalism.REAL
