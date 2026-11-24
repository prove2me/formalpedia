-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.clearedM_of_ode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:29.535427+00:00
-- url     : https://prove2.me/submissions/98236cfb-072b-4657-820b-6b576d77acbb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_alg_first
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_z_mul_zi
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_uPow_neg_two
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_uPow_neg_three
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_C_neg_two
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_dL_uPow
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution {g2 g3 : K} {M : K⟦X⟧}
    (h : dL (uPow (-2) * toL M) ^ 2 = 4 * (uPow (-2) * toL M) ^ 3
      - HahnSeries.C g2 * (uPow (-2) * toL M) - HahnSeries.C g3) : ClearedM g2 g3 M := by
  have hd : dL (uPow (-2) * toL M : LaurentSeries K)
      = uPow (-1) ^ 2 * toL (derivative K M) + (-2) * uPow (-1) ^ 3 * toL M := by
    rw [dL_mul, dL_toL, dL_uPow, C_neg_two, uPow_neg_two, uPow_neg_three]
    ring
  rw [hd, uPow_neg_two] at h
  have e := alg_first (toL X) (uPow (-1)) (toL M) (toL (derivative K M)) (HahnSeries.C g2)
    (HahnSeries.C g3) z_mul_zi h
  unfold ClearedM
  apply toL_injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, HahnSeries.ofPowerSeries_C]
  linear_combination e
end Formalism.L2.Th1.A.WpSh
