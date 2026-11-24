-- Prove2me | solution 1 for Formalism.L2.Th1.A.eq_substInv_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:20:28.963728+00:00
-- url     : https://prove2.me/submissions/af25b4f3-f4fc-43e7-9336-6943e89bbea5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


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
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht : t.subst s = X) :
    t = s.substInvOfIsUnit h1 := by
  have hs : HasSubst s := HasSubst.of_constantCoeff_zero' h0
  have hq : HasSubst (s.substInvOfIsUnit h1) := HasSubst.substInvOfIsUnit s h1
  have key := subst_comp_subst_apply hs hq t
  rw [subst_substInvOfIsUnit_right s h0 h1, ht, subst_X hq, X_subst] at key
  exact key.symm
end Formalism.L2.Th1.A
