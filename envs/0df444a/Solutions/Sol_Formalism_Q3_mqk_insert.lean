-- Prove2me | solution 1 for Formalism.Q3.mqk_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:41.439865+00:00
-- url     : https://prove2.me/submissions/1932420d-1b1d-4447-a10e-ba54f81572b0

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {E : Type*} [Field E] [CharZero E]
omit [CharZero E]
namespace Formalism.Q3
theorem _root_.solution (F : Type*) [Field F] [Algebra F E] {k : ℕ} (α : Fin k → E) (T : Finset (Fin k)) (j : Fin k) :
    mqkField F α (insert j T) =
      (IntermediateField.adjoin (mqkField F α T) {α j}).restrictScalars F := by
  have h := IntermediateField.adjoin_adjoin_left F (α '' (T : Set (Fin k))) {α j}
  refine Eq.trans ?_ h.symm
  unfold mqkField
  rw [Set.union_singleton, Finset.coe_insert, Set.image_insert_eq]
end Formalism.Q3
