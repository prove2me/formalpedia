-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.alpha_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:22.410152+00:00
-- url     : https://prove2.me/submissions/894e80a2-5114-4ddc-bad7-b498202421a7

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Theorems.Thm_Formalism_Q3_CMConjugation_q_pos
import Theorems.Thm_Formalism_Q3_CMConjugation_alpha_sq

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
theorem _root_.solution (hq : Hyp3 q) (hα : IsHost q α) (i : Fin 3) : α i ≠ 0 := by
  intro h0
  have h1 := alpha_sq hα i
  rw [h0, zero_pow two_ne_zero, zero_eq_neg] at h1
  exact (q_pos hq i).ne' (by exact_mod_cast h1)
end Formalism.Q3.CMConjugation
