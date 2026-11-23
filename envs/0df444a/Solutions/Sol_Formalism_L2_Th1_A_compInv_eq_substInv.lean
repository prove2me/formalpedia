-- Prove2me | solution 1 for Formalism.L2.Th1.A.compInv_eq_substInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:23.664157+00:00
-- url     : https://prove2.me/submissions/63ec6e89-824a-4d09-bd40-de6f00e649a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Theorems.Thm_Formalism_L2_Th1_A_eq_substInv_of_right

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
theorem _root_.solution (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s)) :
    compInv s = s.substInvOfIsUnit h1 := by
  have hex : ∃ t : R⟦X⟧, constantCoeff t = 0 ∧ s.subst t = X :=
    ⟨s.substInvOfIsUnit h1, constantCoeff_substInvOfIsUnit s h1,
      subst_substInvOfIsUnit_right s h0 h1⟩
  unfold compInv
  rw [dif_pos hex]
  exact eq_substInv_of_right s h0 h1 _ hex.choose_spec.1 hex.choose_spec.2
end Formalism.L2.Th1.A
