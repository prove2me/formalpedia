-- Prove2me | solution 1 for Formalism.L2.Th1.D.evA_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:58.52069+00:00
-- url     : https://prove2.me/submissions/9a2fe4f3-3472-4613-a627-d39530dbf795

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
theorem _root_.solution : Function.Surjective (evA l 1) := by
  have hle : ringA l ≤ (evK l 1).toRingHom.range := by
    refine Subring.closure_le.mpr fun g hg => ?_
    refine ⟨MonoidAlgebra.of ℤ (muSub l) ⟨g, hg⟩, ?_⟩
    change evK l 1 _ = g
    rw [evK_of, pow_one]
  rintro ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hle hx
  exact ⟨r, Subtype.ext hr⟩
end Formalism.L2.Th1.D
