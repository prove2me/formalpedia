-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_positionAction_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:54.769061+00:00
-- url     : https://prove2.me/submissions/176d7726-8851-4bae-ad4a-d083d5aab95c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_apply
import Theorems.Thm_Formalism_REAL_firstPositionSlice_apply

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (α' : Fin j → Fin n × Fin n) (k : Fin j) (a b : Fin n)
    (F : Arr V n (j+1)) (β : Fin 1 → Fin n × Fin n) :
    sliceLin V n α' (factorAction k.succ a b F) β =
      (if (α' k).1 = a then F (Fin.cons (β 0) (Function.update α' k (b, (α' k).2))) else 0) -
      (if (α' k).2 = b then F (Fin.cons (β 0) (Function.update α' k ((α' k).1, a))) else 0) := by
  rw [firstPositionSlice_apply, factorAction_apply]
  simp only [Fin.cons_succ, ← Fin.cons_update]
end Formalism.REAL
