-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:08.415895+00:00
-- url     : https://prove2.me/submissions/f403ef25-5efc-48c3-9a14-95b32e2c8d8e

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_one
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_mul

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
namespace IsWild
theorem _root_.solution {σ : Ω ≃ₐ[E] Ω} (h : IsWild A σ) (n : ℕ) : IsWild A (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IsWild.one
  | succ n ih => rw [pow_succ]; exact ih.mul h
end IsWild
end Formalism.MainNotions.N.KillingConditions.WildPf
