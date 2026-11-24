-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.algAdjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:16.86891+00:00
-- url     : https://prove2.me/submissions/5709190a-5892-4949-b344-2b2f850744ba

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
theorem _root_.solution (hα : IsHost q α) : Algebra.adjoin ℚ (Set.range α) = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hα.2]
  rfl
end Formalism.Q3.CMConjugation
