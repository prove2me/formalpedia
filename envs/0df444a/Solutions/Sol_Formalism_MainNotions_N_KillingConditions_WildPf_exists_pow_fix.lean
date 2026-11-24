-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.exists_pow_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:54.571652+00:00
-- url     : https://prove2.me/submissions/9a36eb0d-3ccd-40b5-b361-035a00325a23

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Bl_general_b_fact_right_version_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}
namespace Formalism.MainNotions.N.KillingConditions.WildPf
theorem _root_.solution (σ : Ω ≃ₐ[E] Ω) (y : Ω) (hy : IsIntegral E y) : ∃ n : ℕ, n ≠ 0 ∧ (σ ^ n) y = y := by
  first | exact Bl.general_b_fact_right_version.goal1 .. | (apply Bl.general_b_fact_right_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_version.goal1 <;> assumption)
end Formalism.MainNotions.N.KillingConditions.WildPf
