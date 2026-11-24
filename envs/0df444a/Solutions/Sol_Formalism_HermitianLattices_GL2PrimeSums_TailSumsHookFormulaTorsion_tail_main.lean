-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tail_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:19.498751+00:00
-- url     : https://prove2.me/submissions/1f419afe-75fd-4561-8147-b1df23a5d1ec

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_tail_abs
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_sum_pow
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_sum_log
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_w_bound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_one_le_log_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
theorem _root_.solution (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (M : ℕ) (hM : 3 ≤ M) (Q : ℝ) (hQ : 1 ≤ Q) (P E : ℝ) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hβ : ∀ n : ℕ, M ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2))) :
    ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤
      P * ((804 * Real.log (M * Q) ^ 2 + 5000000000) * (M : ℝ) ^ (-((1 : ℝ) / 400))) + 3 * E := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  set l := Real.log (M * Q) with hl
  set m4 := (M : ℝ) ^ (-((1 : ℝ) / 400)) with hm4
  set m8 := (M : ℝ) ^ (-((1 : ℝ) / 800)) with hm8
  have hm4p : 0 < m4 := Real.rpow_pos_of_pos hM' _
  have hm8p : 0 < m8 := Real.rpow_pos_of_pos hM' _
  have hm88 : m8 * m8 = m4 := by
    rw [hm8, hm4, ← Real.rpow_add hM']; congr 1; norm_num
  have hw : ∀ n : ℕ, M ≤ n → (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤
      2 * l ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) + 2 * 1600 ^ 2 * m8 * (n : ℝ) ^ (-((1 : ℝ) / 800)) :=
    fun n hn => w_bound M n (by omega) hn Q hQ
  have h0 : ∀ n : ℕ, M ≤ n →
      P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2) ≤
        P * ((2 * l ^ 2 + 2 * 1600 ^ 2) * m4) + E := by
    intro n hn
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
    have a4 : (n : ℝ) ^ (-((1 : ℝ) / 400)) ≤ m4 :=
      Real.rpow_le_rpow_of_nonpos hM' hMn (by norm_num)
    have a8 : (n : ℝ) ^ (-((1 : ℝ) / 800)) ≤ m8 :=
      Real.rpow_le_rpow_of_nonpos hM' hMn (by norm_num)
    have hlog := one_le_log_nat n (hM.trans hn)
    have b1 : 1 / Real.log (n : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ hlog
    have b2 : 2 * l ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 2 * l ^ 2 * m4 :=
      mul_le_mul_of_nonneg_left a4 (by positivity)
    have b3 : 2 * 1600 ^ 2 * m8 * (n : ℝ) ^ (-((1 : ℝ) / 800)) ≤ 2 * 1600 ^ 2 * m8 * m8 :=
      mul_le_mul_of_nonneg_left a8 (by positivity)
    have b4 : (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤ (2 * l ^ 2 + 2 * 1600 ^ 2) * m4 := by
      have := hw n hn
      have e : 2 * 1600 ^ 2 * m8 * m8 = 2 * 1600 ^ 2 * m4 := by rw [mul_assoc, hm88]
      linarith
    have b5 := mul_le_mul_of_nonneg_left b4 hP
    have b6 := mul_le_mul_of_nonneg_left b1 hE
    linarith
  have h1 : ∀ N : ℕ, M ≤ N → ∑ n ∈ Ioc M N,
      (P * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) + E * (1 / Real.log (n : ℝ) ^ 2)) / n ≤
        P * ((800 * l ^ 2 + 1600 ^ 3) * m4) + E := by
    intro N hN
    have s4 := sum_pow ((1 : ℝ) / 400) (by norm_num) M (by omega) N hN
    have s8 := sum_pow ((1 : ℝ) / 800) (by norm_num) M (by omega) N hN
    have sl := sum_log M (by omega) N hN
    have hlogM := one_le_log_nat M hM
    have sl' : 1 / Real.log (M : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hlogM
    calc _ ≤ ∑ n ∈ Ioc M N, (P * (2 * l ^ 2) * ((n : ℝ) ^ (-((1 : ℝ) / 400)) / n) +
          P * (2 * 1600 ^ 2 * m8) * ((n : ℝ) ^ (-((1 : ℝ) / 800)) / n) +
          E * (1 / Real.log (n : ℝ) ^ 2 / n)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn1 : M ≤ n := (Finset.mem_Ioc.mp hn).1.le
          have hn' : (0 : ℝ) < n := lt_of_lt_of_le hM' (by exact_mod_cast hn1)
          have c1 := mul_le_mul_of_nonneg_left (hw n hn1) hP
          rw [div_le_iff₀ hn']
          have e : (P * (2 * l ^ 2) * ((n : ℝ) ^ (-((1 : ℝ) / 400)) / n) +
            P * (2 * 1600 ^ 2 * m8) * ((n : ℝ) ^ (-((1 : ℝ) / 800)) / n) +
            E * (1 / Real.log (n : ℝ) ^ 2 / n)) * n =
            P * (2 * l ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) + 2 * 1600 ^ 2 * m8 * (n : ℝ) ^ (-((1 : ℝ) / 800)))
             + E * (1 / Real.log (n : ℝ) ^ 2) := by
            field_simp
          rw [e]
          linarith
      _ = P * (2 * l ^ 2) * ∑ n ∈ Ioc M N, ((n : ℝ) ^ (-((1 : ℝ) / 400)) / n) +
          P * (2 * 1600 ^ 2 * m8) * ∑ n ∈ Ioc M N, ((n : ℝ) ^ (-((1 : ℝ) / 800)) / n) +
          E * ∑ n ∈ Ioc M N, (1 / Real.log (n : ℝ) ^ 2 / n) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ ≤ P * (2 * l ^ 2) * (m4 / (1 / 400)) + P * (2 * 1600 ^ 2 * m8) * (m8 / (1 / 800)) + E * 1 := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_of_nonneg_left s4 (by positivity)
          · exact mul_le_mul_of_nonneg_left s8 (by positivity)
          · exact mul_le_mul_of_nonneg_left (sl.trans sl') hE
      _ = P * ((800 * l ^ 2 + 1600 ^ 3) * m4) + E := by
          rw [← hm88]; ring
  have key := tail_abs a S hS M (by omega) _ _ _ hβ h0 h1
  have : 0 ≤ P * m4 := by positivity
  nlinarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
