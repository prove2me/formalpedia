-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_key_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:37.286116+00:00
-- url     : https://prove2.me/submissions/0b45848b-e2a6-4555-a786-61a1c676736e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (j : CF.J) (I : TIdx (CF.mu j))
    (nu : Fin n → ℤ) (h : ¬ DomLE nu (CF.mu j)) :
    qb_ev M F nu (fun i => (CF.vec j I i : F)) = 0 := by
  funext i
  rw [qb_key]
  exact sum_eq_zero fun K _ => if_neg (by intro hK; exact h (by rw [← hK]; exact qb_wtT_le (CF.dom j) K))
end Formalism.InvariantFactorPaths.ColumnFamilies
