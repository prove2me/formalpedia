-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.val_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:43.009651+00:00
-- url     : https://prove2.me/submissions/ce0b4339-e177-481c-ba04-7ae39a98f2ad

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro

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
theorem _root_.solution {σ : Ω ≃ₐ[E] Ω} (h : IsWild A σ) {y : Ω} (hy : y ≠ 0) : A.valuation (σ y / y) = 1 := by
  have := Valuation.map_one_add_of_lt (v := A.valuation) (h y hy)
  rwa [add_sub_cancel] at this
end IsWild
end Formalism.MainNotions.N.KillingConditions.WildPf
