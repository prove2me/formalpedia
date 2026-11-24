-- Prove2me | solution 1 for Formalism.L2.Th1.A.composition_inverse_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:31:40.98285+00:00
-- url     : https://prove2.me/submissions/64da8598-d474-49b2-af97-5ccd55410ddf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Theorems.Thm_Formalism_L2_Th1_A_eq_substInv_of_right
import Theorems.Thm_Formalism_L2_Th1_A_eq_substInv_of_left
import Theorems.Thm_Formalism_L2_Th1_A_compInv_eq_substInv

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
namespace Formalism.L2.Th1.A
theorem _root_.solution : CompInvSpec.{u} := by
  intro R _ s h0 h1
  rw [compInv_eq_substInv s h0 h1]
  refine ⟨constantCoeff_substInvOfIsUnit s h1, subst_substInvOfIsUnit_right s h0 h1,
    subst_substInvOfIsUnit_left s h0 h1, ?_, fun t ht0 ht => eq_substInv_of_right s h0 h1 t ht0 ht,
    fun t _ ht => eq_substInv_of_left s h0 h1 t ht⟩
  rw [coeff_one_substInvOfIsUnit]
  exact h1.val_inv_mul
end Formalism.L2.Th1.A
