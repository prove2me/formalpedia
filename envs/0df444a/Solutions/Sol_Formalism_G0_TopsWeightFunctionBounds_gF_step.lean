-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.gF_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:30.920336+00:00
-- url     : https://prove2.me/submissions/68006c07-d2e0-4d07-abcc-abb6bfe87113

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_two_sub_pos
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_key_id

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) :
    gF L₂ δ j d ev ≤ δ * (if okG L₂ j d ev = true then 1 else 0) + (1 - δ) * gF L₂ δ j (d + 1) (!ev) := by
  have h2 := two_sub_pos h1
  by_cases hj : j = 0
  · subst hj
    cases ev
    · simp only [okG, gF, if_true, Bool.not_false]
      simp
      have k := key_id h1
      rw [one_div, mul_one] at k
      linarith
    · simp only [okG, gF, if_true, Bool.not_true]
      simp
      rw [div_eq_mul_inv]
  · by_cases hd : d < L₂ / 2
    · have hok : okG L₂ j d ev = false := by
        simp only [okG, hj, if_false]
        have : ¬ L₂ < 2 * (d + 1) := by omega
        simp [this]
      rw [hok]
      simp only [gF, hj, if_false]
      have hm1 : max d (L₂ / 2) = L₂ / 2 := by omega
      have hm2 : max (d + 1) (L₂ / 2) = L₂ / 2 := by omega
      have hs : L₂ / 2 - d = (L₂ / 2 - (d + 1)) + 1 := by omega
      rw [hm1, hm2, hs, pow_succ]
      simp; ring_nf; exact le_rfl
    · have hm1 : max d (L₂ / 2) = d := by omega
      have hm2 : max (d + 1) (L₂ / 2) = d + 1 := by omega
      have hs1 : L₂ / 2 - d = 0 := by omega
      have hs2 : L₂ / 2 - (d + 1) = 0 := by omega
      have hlt : L₂ < 2 * (d + 1) := by omega
      simp only [gF, hj, if_false, hm1, hm2, hs1, hs2, pow_zero, one_mul]
      rcases Nat.mod_two_eq_zero_or_one d with hp | hp
      · have hq : (d + 1) % 2 ≠ 0 := by omega
        have hok : okG L₂ j d ev = false := by simp [okG, hj, hq]
        rw [hok]
        simp only [eF, hp, hq, if_true, if_false]
        simp; rw [div_eq_mul_inv]
      · have hq : (d + 1) % 2 = 0 := by omega
        have hp' : d % 2 ≠ 0 := by omega
        have hok : okG L₂ j d ev = true := by simp [okG, hj, hq, hlt]
        rw [hok]
        simp only [eF, hp', hq, if_true, if_false]
        rw [key_id h1]
end Formalism.G0.TopsWeightFunctionBounds
