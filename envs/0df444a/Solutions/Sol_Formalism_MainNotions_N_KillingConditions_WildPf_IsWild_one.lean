-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:41.313479+00:00
-- url     : https://prove2.me/submissions/f7c5cbc9-5ccf-4ebb-bf6a-889a94ff1826

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
theorem _root_.solution : IsWild A (1 : Ω ≃ₐ[E] Ω) := by
  intro y hy
  have : (1 : Ω ≃ₐ[E] Ω) y / y - 1 = 0 := by
    rw [AlgEquiv.one_apply, div_self hy, sub_self]
  rw [this, map_zero]
  exact zero_lt_one
end IsWild
end Formalism.MainNotions.N.KillingConditions.WildPf
