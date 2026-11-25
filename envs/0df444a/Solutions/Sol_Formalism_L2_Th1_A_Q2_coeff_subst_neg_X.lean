-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q2.coeff_subst_neg_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:37:25.201306+00:00
-- url     : https://prove2.me/submissions/beba6c81-e2ee-487c-98e4-ad530c3a3a05

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
import Theorems.Thm_Formalism_L2_Th1_A_Q2_subst_neg_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Q2
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.Q2
theorem _root_.solution (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst (-X : R⟦X⟧)) = (-1) ^ n * coeff n f := by
  rw [subst_neg_X, PowerSeries.coeff_rescale]
end Formalism.L2.Th1.A.Q2
