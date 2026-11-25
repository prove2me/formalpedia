-- Prove2me | solution 1 for Formalism.MainNotions.S.Loc.add_natPred_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:17.319237+00:00
-- url     : https://prove2.me/submissions/95a08db8-115a-4051-b711-f17c66cb0f4c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ComplexConjugate
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
namespace Formalism.MainNotions.S.Loc
theorem _root_.solution (m : ℕ) (s : ℕ+) : m + (s : ℕ) = (m + s.natPred) + 1 := by
  rw [add_assoc, PNat.natPred_add_one]
end Formalism.MainNotions.S.Loc
