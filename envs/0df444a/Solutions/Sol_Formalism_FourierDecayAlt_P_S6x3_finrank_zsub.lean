-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.finrank_zsub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:36.761144+00:00
-- url     : https://prove2.me/submissions/2b6197fd-ebff-4482-bbb4-a31b93e57127

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (A : FI E) (hA : A ≠ 0) : finrank ℤ (zsub E A) = finrank ℚ E := by
  have := fractionalIdeal_rank E (Units.mk0 A hA)
  rw [RingOfIntegers.rank] at this
  exact this
end Formalism.FourierDecayAlt.P.S6x3
