-- Prove2me | solution 1 for Formalism.Q3.mq_algAdjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:01.023704+00:00
-- url     : https://prove2.me/submissions/6c21feb2-715b-440e-b421-70cd65047281

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
theorem _root_.solution (h : IsMQ a α) : Algebra.adjoin ℚ (Set.range α) = ⊤ := by
  have halg : ∀ x ∈ Set.range α, IsAlgebraic ℚ x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, h.2]
  rfl
end Formalism.Q3
