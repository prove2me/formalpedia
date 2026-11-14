-- Prove2me | solution 1 for CountingLLL.ContractedWalk.generating_function_continuous
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:13:47.640205+00:00
-- url     : https://prove2.me/submissions/0a91c107-f15c-4675-a833-4661fda6e0e5

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_recursion
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_bounds

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk

private theorem cubic_lipschitz (θ x y g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1)
    (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*x*g^3) (hhEq : h = 1-θ+θ*y*h^3) :
    |g-h| ≤ θ/(1-3*θ)*|x-y| := by
  have hg2 : g^2 ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hh2 : h^2 ≤ 1 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have hgh : g*h ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hh)]
  have hs0 : 0 ≤ g^2+g*h+h^2 := by positivity
  have hs : g^2+g*h+h^2 ≤ 3 := by nlinarith
  have hp : |g^3-h^3| ≤ 3*|g-h| := by
    rw [show g^3-h^3 = (g-h)*(g^2+g*h+h^2) by ring, abs_mul, abs_of_nonneg hs0]
    nlinarith [mul_nonneg (abs_nonneg (g-h)) (sub_nonneg.mpr hs)]
  have hg3 : 0 ≤ g^3 := pow_nonneg hg0 _
  have hg3le : g^3 ≤ 1 := pow_le_one₀ hg0 hg
  have hpiece : |x*g^3-y*h^3| ≤ |x-y| + 3*|g-h| := by
    have heq : x*g^3-y*h^3 = (x-y)*g^3+y*(g^3-h^3) := by ring
    rw [heq]
    calc
      _ ≤ |(x-y)*g^3|+|y*(g^3-h^3)| := abs_add_le _ _
      _ = |x-y| * g^3 + y * |g^3-h^3| := by rw [abs_mul, abs_mul, abs_of_nonneg hg3, abs_of_nonneg hy0]
      _ ≤ |x-y|+3*|g-h| := by
        nlinarith [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hg3le),
          mul_nonneg (sub_nonneg.mpr hy) (abs_nonneg (g^3-h^3)), mul_nonneg hy0 (sub_nonneg.mpr hp)]
  have hdiff : g-h = θ*(x*g^3-y*h^3) := by nlinarith [hgEq,hhEq]
  have hdabs : |g-h| = θ*|x*g^3-y*h^3| := by rw [hdiff, abs_mul, abs_of_nonneg ht0]
  have hineq : |g-h| ≤ θ*(|x-y| + 3*|g-h|) := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hpiece)]
  have hden : 0 < 1-3*θ := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith

theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) :
    ContinuousOn (generatingFunction θ) (Set.Icc (0:ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  let C := θ/(1-3*θ)
  have hden : 0 < 1-3*θ := by linarith
  have hC : 0 ≤ C := div_nonneg hθ0 (le_of_lt hden)
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro y hy hdist
  have hθ1 : θ ≤ 1 := by linarith
  have hGx := generating_function_bounds θ x hθ1 hx.1 hx.2
  have hGy := generating_function_bounds θ y hθ1 hy.1 hy.2
  have hxEq := generating_function_recursion θ x hθ0 hθ hx.1 hx.2
  have hyEq := generating_function_recursion θ y hθ0 hθ hy.1 hy.2
  have hlip := cubic_lipschitz θ y x (generatingFunction θ y) (generatingFunction θ x)
    hθ0 hθ hy.1 hy.2 hx.1 hx.2 hGy.1 hGy.2 hGx.1 hGx.2 hyEq hxEq
  change |generatingFunction θ y - generatingFunction θ x| ≤ C*|y-x| at hlip
  rw [Real.dist_eq] at hdist ⊢
  have hδid : (C+1)*δ = ε := by dsimp [δ]; field_simp
  have hgap : 0 < δ-|y-x| := by linarith
  nlinarith [mul_nonneg hC (le_of_lt hgap), abs_nonneg (y-x)]
