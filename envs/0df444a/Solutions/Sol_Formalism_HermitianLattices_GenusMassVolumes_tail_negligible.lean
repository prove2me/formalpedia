-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.tail_negligible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:49.139806+00:00
-- url     : https://prove2.me/submissions/40732d59-cf1e-4b94-a586-bc484d5b97e0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HolderExponentialMoments
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
private lemma half_le_gamma_succ (x : ℝ) (hx : 1 ≤ x) (h : 1 / 2 ≤ Real.Gamma x) :
    1 / 2 ≤ Real.Gamma (x + 1) := by
  rw [Real.Gamma_add_one (by linarith)]
  nlinarith
private lemma half_le_gamma_half_nat (n : ℕ) (hn : 2 ≤ n) : 1 / 2 ≤ Real.Gamma ((n : ℝ) / 2) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · norm_num [Real.Gamma_one]
    · have e : ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 := by norm_num
      rw [e, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      have : (1 : ℝ) ≤ Real.sqrt Real.pi := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      linarith
    · have e : (n : ℝ) / 2 = ((n - 2 : ℕ) : ℝ) / 2 + 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hx : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 2)
      rw [e]
      exact half_le_gamma_succ _ (by linarith) (ih (n - 2) (by omega) (by omega))
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : TailNegligible := by
  refine ⟨20, ?_⟩
  intro n Q hn hQ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hnL : (n : ℝ) * Real.log 2 ≤ n * Real.log n := mul_le_mul_of_nonneg_left hL hn0
  have hnl2 : (0.6931471803 : ℝ) * n ≤ n * Real.log 2 := by nlinarith
  have hQpos : 0 < Q := by nlinarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hlogQ : Real.log Q ≤ Q / (2 * n) - 1 + (Real.log 2 + Real.log n) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hQpos h2n)
    rw [Real.log_div hQpos.ne' h2n.ne', Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hm : (n : ℝ) / 2 * Real.log Q ≤
      Q / 4 - n / 2 + n / 2 * Real.log 2 + n / 2 * Real.log n := by
    have h1 := mul_le_mul_of_nonneg_left hlogQ (by linarith : (0 : ℝ) ≤ n / 2)
    have e : (n : ℝ) / 2 * (Q / (2 * n) - 1 + (Real.log 2 + Real.log n)) =
        Q / 4 - n / 2 + n / 2 * Real.log 2 + n / 2 * Real.log n := by
      have hnne : (n : ℝ) ≠ 0 := by linarith
      first | (field_simp; ring) | field_simp | ring
    linarith
  have hG := half_le_gamma_half_nat n hn
  have hQm : 0 < Q ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hQpos _
  have h4Qm : 0 < 4 * Q ^ ((n : ℝ) / 2) := by linarith
  have h2Qm : 0 < 2 * Q ^ ((n : ℝ) / 2) := by linarith
  have hE : (3 : ℝ) ≤ -(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2) := by nlinarith
  have hexp : Real.exp (-(Q / 2)) * (4 * Q ^ ((n : ℝ) / 2)) ≤ Real.exp (-(n : ℝ)) := by
    rw [Real.rpow_def_of_pos hQpos]
    have h4 : (4 : ℝ) ≤ Real.exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2)) := by
      have := Real.add_one_le_exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2))
      linarith
    calc Real.exp (-(Q / 2)) * (4 * Real.exp (Real.log Q * ((n : ℝ) / 2)))
        ≤ Real.exp (-(Q / 2)) * (Real.exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2)) *
            Real.exp (Real.log Q * ((n : ℝ) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (-(n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  calc Real.exp (-(Q / 2))
      = Real.exp (-(Q / 2)) * (4 * Q ^ ((n : ℝ) / 2)) / (4 * Q ^ ((n : ℝ) / 2)) := by
        rw [mul_div_assoc, div_self h4Qm.ne', mul_one]
    _ ≤ Real.exp (-(n : ℝ)) / (4 * Q ^ ((n : ℝ) / 2)) := by gcongr
    _ = Real.exp (-(n : ℝ)) * (1 / 2 / (2 * Q ^ ((n : ℝ) / 2))) := by
        rw [div_div, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, mul_one_div]
    _ ≤ Real.exp (-(n : ℝ)) * (Real.Gamma ((n : ℝ) / 2) / (2 * Q ^ ((n : ℝ) / 2))) := by
        gcongr
end Formalism.HermitianLattices.GenusMassVolumes
