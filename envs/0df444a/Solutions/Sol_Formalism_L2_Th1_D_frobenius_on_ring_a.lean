-- Prove2me | solution 1 for Formalism.L2.Th1.D.frobenius_on_ring_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:02.752864+00:00
-- url     : https://prove2.me/submissions/cb40a6c8-3884-4cdb-8cfe-11351c917e87

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
import Theorems.Thm_Formalism_L2_Th1_D_evA_of
import Theorems.Thm_Formalism_L2_Th1_D_evA_surj
import Theorems.Thm_Formalism_L2_Th1_D_evA_ker
import Theorems.Thm_Formalism_L2_Th1_D_evA_congr

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
theorem _root_.solution : FrobA := by
  intro l _
  refine ⟨(evA l 1).liftOfSurjective (evA_surj l) ⟨evA l l, evA_ker l⟩, fun ζ hζ => ?_, fun x => ?_⟩
  · have h1 : evA l 1 (MonoidAlgebra.of ℤ (muSub l) ⟨ζ, hζ⟩) = ζ := by
      rw [evA_of, pow_one]
    conv_lhs => rw [← h1]
    rw [RingHom.liftOfSurjective_comp_apply]
    change evA l l _ = _
    rw [evA_of]
  · obtain ⟨r, rfl⟩ := evA_surj l x
    rw [RingHom.liftOfSurjective_comp_apply]
    exact evA_congr l r
end Formalism.L2.Th1.D
