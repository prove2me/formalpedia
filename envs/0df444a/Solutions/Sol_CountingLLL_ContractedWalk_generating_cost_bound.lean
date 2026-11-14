-- Prove2me | solution 1 for CountingLLL.ContractedWalk.generating_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:48:33.648258+00:00
-- url     : https://prove2.me/submissions/79f25e5a-7fd2-4b73-9989-ebb4cbd40491

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_bounds
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_continuous
import Theorems.Thm_CountingLLL_ReciprocalTest_source_cost_integral_bound
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped Interval

private theorem point_bound (θ z g : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    z*(1+g+g^2)/(1-θ*z*(1+g+g^2)) ≤ 3*z/(1-3*θ*z) := by
  let a : ℝ := 1+g+g^2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 3 := by dsimp [a]; nlinarith [sq_nonneg (g-1)]
  have hθz : 0 ≤ θ*z := mul_nonneg hθ0 hz0
  have hθza : θ*z*a ≤ 3*θ*z := by nlinarith [mul_nonneg hθz (sub_nonneg.mpr ha1)]
  have hθzmax : θ*z ≤ 9/40 := by nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) hz0, mul_nonneg hθ0 (sub_nonneg.mpr hz1)]
  have hd1 : 0 < 1-3*θ*z := by linarith
  have hd2 : 0 < 1-θ*z*a := by linarith
  change z*a/(1-θ*z*a) ≤ 3*z/(1-3*θ*z)
  apply (div_le_div_iff₀ hd2 hd1).2
  nlinarith [mul_nonneg hz0 (sub_nonneg.mpr ha1)]

theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40) :
    (∫ z in (0:ℝ)..1, z*(1+generatingFunction θ z+(generatingFunction θ z)^2)/
      (1-θ*z*(1+generatingFunction θ z+(generatingFunction θ z)^2))) < (74/25:ℝ) := by
  let G := generatingFunction θ
  let A : ℝ → ℝ := fun z => 1+G z+(G z)^2
  have hG : ContinuousOn G (Set.Icc (0:ℝ) 1) := generating_function_continuous θ hθ0 (by linarith)
  have hA : ContinuousOn A (Set.Icc (0:ℝ) 1) := by
    unfold A
    fun_prop
  have hden (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) : 1-θ*z*A z ≠ 0 := by
    have hg := generating_function_bounds θ z (by linarith) hz.1 hz.2
    change 0 ≤ G z ∧ G z ≤ 1 at hg
    have ha0 : 0 ≤ A z := by dsimp [A]; nlinarith [sq_nonneg (G z)]
    have ha1 : A z ≤ 3 := by dsimp [A]; nlinarith [sq_nonneg (G z-1)]
    have hθz : 0 ≤ θ*z := mul_nonneg hθ0 hz.1
    have hθza : θ*z*A z ≤ 3*θ*z := by nlinarith [mul_nonneg hθz (sub_nonneg.mpr ha1)]
    have hh : 0 ≤ ((9/40:ℝ)-θ)*z := mul_nonneg (sub_nonneg.mpr hθ1) hz.1
    have hz1 : z ≤ 1 := hz.2
    have hp : 0 < 1-θ*z*A z := by nlinarith
    linarith
  have hcont : ContinuousOn (fun z => z*A z/(1-θ*z*A z)) (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hden
  have hi : IntervalIntegrable (fun z => z*A z/(1-θ*z*A z)) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have hden' (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) : 1-3*θ*z ≠ 0 := by
    have hh : 0 ≤ ((9/40:ℝ)-θ)*z := mul_nonneg (sub_nonneg.mpr hθ1) hz.1
    have hz1 : z ≤ 1 := hz.2
    nlinarith
  have hcont' : ContinuousOn (fun z : ℝ => 3*z/(1-3*θ*z)) (Set.Icc 0 1) := by
    apply ContinuousOn.div <;> try fun_prop
    exact hden'
  have hi' : IntervalIntegrable (fun z : ℝ => 3*z/(1-3*θ*z)) volume 0 1 :=
    hcont'.intervalIntegrable_of_Icc (by norm_num)
  have hle : (∫ z in (0:ℝ)..1, z*A z/(1-θ*z*A z)) ≤ ∫ z in (0:ℝ)..1, 3*z/(1-3*θ*z) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi hi'
    intro z hz
    have hg := generating_function_bounds θ z (by linarith) hz.1 hz.2
    exact point_bound θ z (G z) hθ0 hθ1 hz.1 hz.2 hg.1 hg.2
  exact lt_of_le_of_lt hle (CountingLLL.ReciprocalTest.source_cost_integral_bound θ hθ0 hθ1)
