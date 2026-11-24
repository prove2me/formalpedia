-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.log_sum_exp_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:00.722824+00:00
-- url     : https://prove2.me/submissions/30bd7f88-ba7a-461a-8cf6-ba1c9dd406e2

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LogSumExpBoundHolds
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_exp_ge_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.D.LogSumExp := by
  intro ι _ w y M hw hw1 hmean hy
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨j0⟩ := hne
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hy j0)
  set S := ∑ j, w j * Real.exp (y j) with hS
  set V := ∑ j, w j * y j ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  rcases eq_or_lt_of_le hM0 with hM | hM
  · subst hM
    have hy0 : ∀ j, y j = 0 := fun j => abs_nonpos_iff.mp (hy j)
    have : S = 1 := by simp [hS, hy0, hw1]
    rw [this]
    simp
  · set t := min 1 M⁻¹ with ht
    have ht0 : 0 < t := lt_min one_pos (inv_pos.mpr hM)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htM : t * M ≤ 1 := by
      calc t * M ≤ M⁻¹ * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = 1 := inv_mul_cancel₀ hM.ne'
    have hty : ∀ j, |t * y j| ≤ 1 := by
      intro j
      rw [abs_mul, abs_of_pos ht0]
      calc t * |y j| ≤ t * M := mul_le_mul_of_nonneg_left (hy j) ht0.le
        _ ≤ 1 := htM
    have hVM : V ≤ M ^ 2 := by
      calc V ≤ ∑ j, w j * M ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (hw j)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hy j) 2
        _ = M ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
    set T := ∑ j, w j * Real.exp (t * y j) with hT
    have hT1 : 1 + t ^ 2 * V / 3 ≤ T := by
      calc 1 + t ^ 2 * V / 3 = ∑ j, w j * (1 + t * y j + (t * y j) ^ 2 / 3) := by
            simp only [mul_add, Finset.sum_add_distrib, mul_one, hw1]
            have e1 : ∑ j, w j * (t * y j) = t * ∑ j, w j * y j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
            have e2 : ∑ j, w j * ((t * y j) ^ 2 / 3) = t ^ 2 * V / 3 := by
              rw [hV, Finset.mul_sum, Finset.sum_div]
              exact Finset.sum_congr rfl (fun j _ => by ring)
            rw [e1, e2, hmean]; ring
        _ ≤ T := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (exp_ge_quad (hty j)) (hw j))
    have hu : t ^ 2 * V ≤ 1 := by
      calc t ^ 2 * V ≤ t ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hVM (sq_nonneg _)
        _ = (t * M) ^ 2 := by ring
        _ ≤ 1 := by
          have : 0 ≤ t * M := mul_nonneg ht0.le hM.le
          nlinarith
    have hTpos : 0 < T := by
      have : 0 ≤ t ^ 2 * V := mul_nonneg (sq_nonneg _) hV0
      linarith
    have hlogT : t ^ 2 * V / 4 ≤ Real.log T := by
      set u := t ^ 2 * V / 3 with hu'
      have hu0 : 0 ≤ u := by positivity
      have hlog1 : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u) := Real.one_sub_inv_le_log_of_pos (by linarith)
      have hmono : Real.log (1 + u) ≤ Real.log T := Real.log_le_log (by linarith) hT1
      have : t ^ 2 * V / 4 ≤ 1 - (1 + u)⁻¹ := by
        rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hJ : T ^ (1 / t) ≤ S := by
      have h := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ) w (fun j => Real.exp (t * y j))
        (fun j _ => hw j) hw1 (fun j _ => (Real.exp_pos _).le) (p := 1 / t)
        (by rw [le_div_iff₀ ht0]; linarith)
      refine h.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Real.exp_mul]
      congr 2
      field_simp
    have hlogJ : (1 / t) * Real.log T ≤ Real.log S := by
      rw [← Real.log_rpow hTpos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hTpos _) hJ
    have key : t * V / 4 ≤ (1 / t) * Real.log T := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ht0]
      nlinarith
    linarith
end Formalism.NuclearRankWeightBounds.P
