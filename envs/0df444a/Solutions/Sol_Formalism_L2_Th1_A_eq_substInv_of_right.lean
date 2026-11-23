-- Prove2me | solution 1 for Formalism.L2.Th1.A.eq_substInv_of_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:21.818814+00:00
-- url     : https://prove2.me/submissions/0ef77359-1ad7-4ff7-96e4-c86c49029a2f

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
    (t : R⟦X⟧) (ht0 : constantCoeff t = 0) (ht : s.subst t = X) :
    t = s.substInvOfIsUnit h1 := by
  have hs : HasSubst s := HasSubst.of_constantCoeff_zero' h0
  have hT : HasSubst t := HasSubst.of_constantCoeff_zero' ht0
  have key := subst_comp_subst_apply hs hT (s.substInvOfIsUnit h1)
  rw [subst_substInvOfIsUnit_left s h0 h1, subst_X hT, ht, X_subst] at key
  exact key
end Formalism.L2.Th1.A
