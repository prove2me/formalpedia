-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.gF_lb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:30.283181+00:00
-- url     : https://prove2.me/submissions/13da3ad9-9225-4b4a-928d-35a33bf50d47

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_d_le_one
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_two_sub_pos
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_le_hi
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_eF_lb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (j : ℕ) (ev : Bool) :
    aF L₂ δ ≤ gF L₂ δ j 0 ev := by
  have h1 := d_le_one h0 hL hLδ
  have h2 := two_sub_pos h1
  have hLr : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL

  have hbase : aF L₂ δ ≤ (1 - δ) / (2 - δ) := by
    unfold aF
    rw [le_div_iff₀ h2]
    nlinarith
  unfold gF
  split_ifs with hj
  · exact hbase
  · exact hbase.trans (lo_le_hi h0 h1)
  ·
    have hh : L₂ / 2 + 1 ≤ L₂ := by omega
    have hbern : 1 - ((L₂ / 2 + 1 : ℕ) : ℝ) * δ ≤ (1 - δ) ^ (L₂ / 2 + 1) := by
      have := one_add_mul_le_pow (a := -δ) (by linarith) (L₂ / 2 + 1)
      simpa [sub_eq_add_neg, mul_neg] using this
    have hcast : ((L₂ / 2 + 1 : ℕ) : ℝ) ≤ L₂ := by exact_mod_cast hh
    have he := eF_lb h0 h1 (max 0 (L₂ / 2))
    have hp0 : 0 ≤ (1 - δ) ^ (L₂ / 2) := pow_nonneg (by linarith) _
    have hstep : (1 - δ) ^ (L₂ / 2) * ((1 - δ) / (2 - δ)) ≤
        (1 - δ) ^ (L₂ / 2 - 0) * eF δ (max 0 (L₂ / 2)) := by
      simp only [Nat.sub_zero]
      exact mul_le_mul_of_nonneg_left he hp0
    refine le_trans ?_ hstep
    have hq : (1 - δ) ^ (L₂ / 2) * ((1 - δ) / (2 - δ)) = (1 - δ) ^ (L₂ / 2 + 1) / (2 - δ) := by
      rw [pow_succ]; ring
    rw [hq, le_div_iff₀ h2]
    unfold aF
    have hpow1 : (1 - δ) ^ (L₂ / 2 + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpow0 : 0 ≤ (1 - δ) ^ (L₂ / 2 + 1) := pow_nonneg (by linarith) _
    nlinarith
end Formalism.G0.TopsWeightFunctionBounds
