-- Prove2me | solution 1 for Formalism.L2.Th1.D.int_fermat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:01.319313+00:00
-- url     : https://prove2.me/submissions/51eee283-f46b-4a6a-a886-bd73be87a9bb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.L2.Th1.D
theorem _root_.solution (a : ℤ) : ∃ c : ℤ, a - a ^ l = (l : ℤ) * c := by
  have : ((a - a ^ l : ℤ) : ZMod l) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
end Formalism.L2.Th1.D
