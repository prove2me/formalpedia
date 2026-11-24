-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.val_intCast_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:12.822563+00:00
-- url     : https://prove2.me/submissions/8f91346c-83a2-4dc2-ae91-1f476698d46e

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
theorem _root_.solution (a : ℤ) : A.valuation ((a : ℤ) : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (intCast_mem A a)
end Formalism.MainNotions.N.KillingConditions.WildPf
