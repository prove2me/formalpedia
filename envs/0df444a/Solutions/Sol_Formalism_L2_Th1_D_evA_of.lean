-- Prove2me | solution 1 for Formalism.L2.Th1.D.evA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:19.791281+00:00
-- url     : https://prove2.me/submissions/05ee4352-77eb-45db-9d5f-550d91105a25

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
import Theorems.Thm_Formalism_L2_Th1_D_evA_coe

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
theorem _root_.solution (k : ℕ) (g : muSub l) :
    evA l k (MonoidAlgebra.of ℤ (muSub l) g) = (⟨g, Subring.subset_closure g.2⟩ : ringA l) ^ k := by
  apply Subtype.ext
  rw [evA_coe, evK_of]
  rfl
end Formalism.L2.Th1.D
