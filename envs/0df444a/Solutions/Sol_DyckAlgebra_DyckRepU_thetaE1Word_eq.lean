-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.thetaE1Word_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:22:10.392492+00:00
-- url     : https://prove2.me/submissions/0931c4f3-665c-46df-a0f7-005df0ec4428

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
import Theorems.Thm_DyckAlgebra_DyckRepU_w1_sub_one
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (hlevel : ρ.level = 0) :
    ρ.thetaE1Word = ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord) := by
  have hc : cQ2 = -1 := by simpa [hlevel] using ρ.Q2scalar
  have hQ : ρ.zz 1 * ρ.dp = -(ρ.yy 1 * ρ.dps) := by
    simpa [hc] using ρ.Q2
  have hw : ρ.w 1 - 1 = -(ρ.u • (ρ.w 1 * ρ.yy 1)) := ρ.w1_sub_one
  unfold thetaE1Word e1Word dPositiveSeries dOneWord Θdp sElt
  rw [sub_mul, one_mul]
  have hs : ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1) * ρ.dp =
      -(ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps)) := by
    rw [smul_mul_assoc, mul_assoc (ρ.w 1 * ρ.yy 1), hQ]
    simp only [mul_neg, smul_neg, mul_assoc]
  rw [hs]
  have hcorr :
      ρ.dm * ρ.w 1 * (-ρ.yy 1) * ρ.dps - ρ.dm * (-ρ.yy 1) * ρ.dps =
        ρ.dm * (ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps)) := by
    have hmul := congrArg (fun x => ρ.dm * x * (-ρ.yy 1) * ρ.dps) hw
    simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc,
      mul_smul_comm, mul_assoc, one_mul, neg_neg] at hmul ⊢
    rw [neg_sub] at hmul
    rw [sub_eq_add_neg] at hmul
    simpa only [sub_neg_eq_add, neg_add_rev, neg_neg, add_comm] using hmul
  calc
    ρ.dm * (ρ.dp - -(ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps))) =
        ρ.dm * ρ.dp + ρ.dm * (ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps)) := by
          rw [sub_neg_eq_add, mul_add]
    _ = ρ.dm * ρ.dp +
        (ρ.dm * ρ.w 1 * (-ρ.yy 1) * ρ.dps - ρ.dm * (-ρ.yy 1) * ρ.dps) := by rw [hcorr]
end DyckAlgebra.DyckRepU
