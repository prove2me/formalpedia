-- Prove2me | solution 1 for Formalism.IncomingBounds.padicValuationGain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:16.440306+00:00
-- url     : https://prove2.me/submissions/8d3d7e3e-9cf8-4a66-9d07-6d1e003bf90f

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
private theorem one_add_mul_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : 1 + k * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg hx hx),
      mul_le_mul_of_nonneg_right ih (by linarith : (0:ℝ) ≤ 1 + x)]
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : ValGain := by
  intro l hl
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hB : 0 < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro n hn
    have hle : l ^ padicValNat l n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hleR : (l : ℝ) ^ padicValNat l n ≤ n := by exact_mod_cast hle
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le (padicValNat l n)
    rw [show (1 : ℝ) + ((l : ℝ) - 1) = l by ring] at hb
    rw [le_sub_iff_add_le, div_add' _ _ _ hB.ne', div_le_div_iff_of_pos_right hB]
    linarith
  · intro e
    unfold rho
    have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
    have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) ^ 2 - 1) hA.le e
    rw [show (1 : ℝ) + ((l : ℝ) ^ 2 - 1) = (l : ℝ) ^ 2 by ring] at hb
    have hm := mul_le_mul_of_nonneg_right hb (one_div_pos.2 hA).le
    have he : (1 + (e : ℝ) * ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) =
        1 / ((l : ℝ) ^ 2 - 1) + e := by
      linear_combination (e : ℝ) * hq
    linarith
end Formalism.IncomingBounds
