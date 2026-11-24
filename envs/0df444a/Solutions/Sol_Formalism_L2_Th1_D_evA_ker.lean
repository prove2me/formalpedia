-- Prove2me | solution 1 for Formalism.L2.Th1.D.evA_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:56.866824+00:00
-- url     : https://prove2.me/submissions/19b143a5-eb58-4b30-9a2f-9afeac1542f5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
import Theorems.Thm_Formalism_L2_Th1_D_evK_ker
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
theorem _root_.solution : RingHom.ker (evA l 1) ≤ RingHom.ker (evA l l) := by
  intro r hr
  rw [RingHom.mem_ker] at hr ⊢
  apply Subtype.ext
  rw [evA_coe]
  exact evK_ker l r (by rw [← evA_coe, hr]; rfl)
end Formalism.L2.Th1.D
