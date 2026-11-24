-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tail_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:37.107216+00:00
-- url     : https://prove2.me/submissions/b5f982ca-64bf-43ef-872d-845037af73dc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_abel

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
    (M : ℕ) (hM : 1 ≤ M) (β : ℕ → ℝ) (B₀ B₁ : ℝ)
    (hβ : ∀ n, M ≤ n → ‖∑ k ∈ Icc 1 n, a k‖ ≤ n * β n)
    (h0 : ∀ n, M ≤ n → β n ≤ B₀)
    (h1 : ∀ N, M ≤ N → ∑ n ∈ Ioc M N, β n / n ≤ B₁) :
    ‖S - ∑ n ∈ Icc 1 M, a n / (n : ℂ)‖ ≤ 2 * B₀ + B₁ := by
  have hpos : ∀ n, M ≤ n → 0 ≤ β n := by
    intro n hn
    have h := (norm_nonneg _).trans (hβ n hn)
    have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    exact nonneg_of_mul_nonneg_right h hn'
  have hb : ∀ n, M ≤ n → ‖(∑ k ∈ Icc 1 n, a k) / ((n : ℂ) + 1)‖ ≤ β n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have e : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_div, e, div_le_iff₀ (by positivity)]
    have := hβ n hn
    have := hpos n hn
    nlinarith
  have hc : ∀ n, M ≤ n → ‖(∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖ ≤ β n / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have e : (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn'.ne'
      have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp
      ring
    rw [norm_mul, e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h3 := hβ n hn
    have h4 := hpos n hn
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hn']
    nlinarith [mul_nonneg hn'.le h4, mul_nonneg (mul_nonneg hn'.le hn'.le) h4]
  refine le_of_tendsto ((hS.sub_const _).norm) ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  rw [abel a M N hN]
  calc _ ≤ ‖(∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1)‖ + ‖(∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1)‖ +
        ‖∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ B₀ + B₀ + ∑ n ∈ Ioc M N, β n / n := by
        refine add_le_add (add_le_add ((hb N hN).trans (h0 N hN)) ((hb M le_rfl).trans (h0 M le_rfl))) ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        exact hc n (Finset.mem_Ioc.mp hn).1.le
    _ ≤ 2 * B₀ + B₁ := by have := h1 N hN; linarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
