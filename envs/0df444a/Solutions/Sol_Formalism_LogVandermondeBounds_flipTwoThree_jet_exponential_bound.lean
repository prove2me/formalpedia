-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.jet_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:28.690802+00:00
-- url     : https://prove2.me/submissions/aa532d53-a1f4-4bcb-9fd3-d1220966567d

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution : MinRatioPowerExponentialBound := by
  intro n g hg
  simp only
  have hg0 : (0:ℝ) < g := by exact_mod_cast hg
  have hE : (4:ℝ) ≤ 2 * Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  by_cases hng : n ≤ g
  · have he : (if n = 0 then (1:ℝ) else min 1 ((g:ℝ)/n)) = 1 := by
      split_ifs with h
      · rfl
      · have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h
        apply min_eq_left
        rw [le_div_iff₀ hn, one_mul]
        exact_mod_cast hng
    rw [he]
    simp only [one_pow, inv_one, one_mul]
    calc (1+1:ℝ)^(n+g) ≤ (1+1)^(g+g) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 4^g := by rw [show g + g = 2 * g by ring, pow_mul]; norm_num
      _ ≤ (2 * Real.exp 1)^g := pow_le_pow_left₀ (by norm_num) hE g
      _ ≤ _ := pow_le_pow_left₀ (by positivity)
          (le_mul_of_one_le_right (by positivity) (le_max_left _ _)) g
  · push Not at hng
    have hn0 : n ≠ 0 := by omega
    have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hgn : (g:ℝ)/n < 1 := by
      rw [div_lt_one hn]; exact_mod_cast hng
    have he : (if n = 0 then (1:ℝ) else min 1 ((g:ℝ)/n)) = (g:ℝ)/n := by
      rw [if_neg hn0]; exact min_eq_right hgn.le
    rw [he]
    have hmax : max 1 ((n:ℝ)/g) = (n:ℝ)/g := by
      apply max_eq_right
      rw [le_div_iff₀ hg0, one_mul]; exact_mod_cast hng.le
    rw [hmax]
    have hx0 : 0 < (g:ℝ)/n := by positivity
    have h1 : (1+(g:ℝ)/n)^n ≤ Real.exp 1 ^ g := by
      calc (1+(g:ℝ)/n)^n ≤ (Real.exp ((g:ℝ)/n))^n :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((g:ℝ)/n)]) n
        _ = Real.exp (n * ((g:ℝ)/n)) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp (g * 1) := by congr 1; field_simp
        _ = Real.exp 1 ^ g := Real.exp_nat_mul 1 g
    have h2 : (1+(g:ℝ)/n)^g ≤ 2^g := pow_le_pow_left₀ (by positivity) (by linarith) g
    have h3 : (((g:ℝ)/n)^g)⁻¹ = ((n:ℝ)/g)^g := by rw [← inv_pow, inv_div]
    rw [pow_add, h3, mul_pow, mul_pow]
    calc ((n:ℝ)/g)^g * ((1+(g:ℝ)/n)^n * (1+(g:ℝ)/n)^g)
        ≤ ((n:ℝ)/g)^g * (Real.exp 1 ^ g * 2^g) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2^g * Real.exp 1 ^ g * ((n:ℝ)/g)^g := by ring
end Formalism.LogVandermondeBounds.flipTwoThree
