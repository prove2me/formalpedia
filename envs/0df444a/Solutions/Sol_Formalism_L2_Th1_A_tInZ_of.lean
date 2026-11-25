-- Prove2me | solution 1 for Formalism.L2.Th1.A.tInZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:17.83809+00:00
-- url     : https://prove2.me/submissions/fb2ceb8f-b769-4f70-bda3-93668b734b95

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_uPow_mul_sq
import Theorems.Thm_Formalism_L2_Th1_A_Two_tS_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Two
namespace Formalism.L2.Th1.A
theorem _root_.solution (hS : WpShape.{u}) : TInZ.{u} := by
  intro K _ _ W xP
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  have h1 := Two.tS_mul W xP
  have hw := (hS K W).1
  unfold wpL at hw
  have hP : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := Two.uPow_mul_sq
  simp only [map_mul, map_sub, map_add, map_one, map_pow, HahnSeries.ofPowerSeries_C]
  linear_combination (-(toL ((tS W xP).subst (expSer W)) * toL X ^ 2)) * hw + toL X ^ 2 * h1
    + (-(toL ((tS W xP).subst (expSer W)))) * hP
end Formalism.L2.Th1.A
