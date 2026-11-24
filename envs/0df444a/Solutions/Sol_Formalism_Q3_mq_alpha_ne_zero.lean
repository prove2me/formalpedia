-- Prove2me | solution 1 for Formalism.Q3.mq_alpha_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:36.350074+00:00
-- url     : https://prove2.me/submissions/6daf5d00-a766-4ebb-a7c9-7134c85a0b8b

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois

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
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}
namespace Formalism.Q3
theorem _root_.solution (h : IsMQ a α) (ha : ∀ i, a i ≠ 0) (i : Fin k) : α i ≠ 0 := by
  intro h0
  have h2 := h.1 i
  rw [h0, zero_pow two_ne_zero] at h2
  exact ha i (by exact_mod_cast h2.symm)
end Formalism.Q3
