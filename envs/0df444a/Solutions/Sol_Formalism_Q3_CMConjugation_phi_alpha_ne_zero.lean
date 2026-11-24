-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.phi_alpha_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:20.569732+00:00
-- url     : https://prove2.me/submissions/49f64dc4-8508-4ae9-b9ed-5fbfeb377cb0

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Theorems.Thm_Formalism_Q3_CMConjugation_alpha_ne_zero

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
theorem _root_.solution (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (i : Fin 3) :
    φ (α i) ≠ 0 := by
  rw [map_ne_zero]; exact alpha_ne_zero hq hα i
end Formalism.Q3.CMConjugation
