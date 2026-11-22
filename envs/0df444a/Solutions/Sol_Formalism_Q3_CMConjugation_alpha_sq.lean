-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.alpha_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:22.256302+00:00
-- url     : https://prove2.me/submissions/410ed8b7-e3e3-4337-b107-8d5d30a6a06c

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
namespace Formalism.Q3.CMConjugation
theorem _root_.solution (hα : IsHost q α) (i : Fin 3) : α i ^ 2 = -(q i : E) := by
  rw [hα.1 i]; push_cast; ring
end Formalism.Q3.CMConjugation
