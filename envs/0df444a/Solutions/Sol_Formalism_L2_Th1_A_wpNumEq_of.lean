-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpNumEq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:03.709266+00:00
-- url     : https://prove2.me/submissions/09fbea96-47fe-4119-b8e6-82c33176c53f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
import Theorems.Thm_Formalism_L2_Th1_A_BridgeK_cW_succ
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
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
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open BridgeK Formalism.L2.Th1.CM
namespace Formalism.L2.Th1.A
theorem _root_.solution (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpNumEq := by
  unfold WpNumEq
  intro K _ _ W
  obtain ⟨_, h0, hodd, _, _⟩ := hS K W
  constructor
  · ext n
    unfold wpNum
    rw [coeff_mk, map_add, coeff_one, coeff_X_pow_mul']
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.lt_or_ge j 1 with hj | hj
      · interval_cases j
        simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1)),
          if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (show 2 ≤ 2 * (i + 1) by omega),
          Nat.mul_div_cancel_left (i + 1) (by norm_num : 0 < 2),
          show 2 * (i + 1) - 2 = 2 * i by omega, cW_succ hS hR W i, zero_add]
    · rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
        if_neg (show 2 * j + 1 ≠ 0 by omega), zero_add]
      split_ifs with h
      · rw [show 2 * j + 1 - 2 = 2 * (j - 1) + 1 by omega, hodd _ (odd_two_mul_add_one (j - 1))]
      · rfl
  · ext n
    unfold wpDen
    rw [coeff_mk, map_sub, coeff_one, mul_assoc (C (1 / 2 : K)) (X ^ 3) (derivative K (wpReg W)),
      coeff_C_mul, coeff_X_pow_mul']
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j <;> simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
        rw [if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1 + 1)),
          if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (show 3 ≤ 2 * (i + 1 + 1) by omega),
          Nat.mul_div_cancel_left (i + 1 + 1) (by norm_num : 0 < 2),
          show 2 * (i + 1 + 1) - 3 = 2 * i + 1 by omega, coeff_derivative,
          show 2 * i + 1 + 1 = 2 * (i + 1) by ring, cW_succ hS hR W (i + 1)]
        push_cast
        ring
    · rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
        if_neg (show 2 * j + 1 ≠ 0 by omega)]
      split_ifs with h
      · rw [show 2 * j + 1 - 3 = 2 * (j - 1) by omega, coeff_derivative,
          hodd _ (odd_two_mul_add_one (j - 1))]
        ring
      · ring
end Formalism.L2.Th1.A
