-- Prove2me | solution 1 for Formalism.L2.Th1.A.composition_inverse_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:09.45129+00:00
-- url     : https://prove2.me/submissions/485c86e3-2486-4af2-94a7-5c8176825098

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Theorems.Thm_Formalism_L2_Th1_A_eq_substInv_of_right
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
theorem _root_.solution : CompInvMap.{u, v} := by
  intro R S _ _ φ s h0 h1
  have h0' : constantCoeff (PowerSeries.map φ s) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have h1' : IsUnit (coeff 1 (PowerSeries.map φ s)) := by
    rw [coeff_map]; exact h1.map φ
  rw [compInv_eq_substInv _ h0' h1', compInv_eq_substInv s h0 h1]
  apply eq_substInv_of_right _ h0' h1'
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_substInvOfIsUnit, map_zero]
  · have := PowerSeries.map_subst (HasSubst.substInvOfIsUnit s h1) (h := φ) s
    rw [subst_substInvOfIsUnit_right s h0 h1] at this
    rw [← PowerSeries.map_X φ]
    exact this.symm
end Formalism.L2.Th1.A
