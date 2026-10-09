-- Prove2me | solution 1 for ConnesGreen.primeOverlapLoss_continuous
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T03:01:36.109778+00:00
-- url     : https://prove2.me/submissions/34d7d3cb-5297-4324-9cdc-4249499503bf

import Definitions.Def_ConnesGreen_prime_overlap_loss
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen
namespace ConnesGreen
theorem primeOverlapLoss_eq_fixed_sum (T R : ℝ) (hTR : T ≤ R) (g : ℝ → ℂ) :
    primeOverlapLoss T g = ∑ n ∈ activePrimePowerFinset R,
      2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        min (∫ s : ℝ, ‖g s‖ ^ 2)
          (2 * physicalTestEnergy g * max (2 * T - Real.log n) 0) := by
  unfold primeOverlapLoss
  apply Finset.sum_subset
  · intro n hn
    have hm := (mem_activePrimePowerFinset T n).mp hn
    exact (mem_activePrimePowerFinset R n).mpr ⟨hm.1, lt_of_lt_of_le hm.2 (by linarith)⟩
  · intro n hnR hnT
    have hm := (mem_activePrimePowerFinset R n).mp hnR
    have hlog : 2*T ≤ Real.log n := by
      by_contra h
      exact hnT ((mem_activePrimePowerFinset T n).mpr ⟨hm.1, by linarith⟩)
    rw [max_eq_right (by linarith), mul_zero,
      min_eq_right (integral_nonneg (fun s => sq_nonneg ‖g s‖)), mul_zero]
end ConnesGreen
theorem solution (g : ℝ → ℂ) :
    Continuous (fun T : ℝ => primeOverlapLoss T g) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  let R := T+1
  have hc : Continuous (fun t : ℝ => ∑ n ∈ activePrimePowerFinset R,
      2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        min (∫ s : ℝ, ‖g s‖ ^ 2)
          (2 * physicalTestEnergy g * max (2 * t - Real.log n) 0)) := by
    fun_prop
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show T < R by dsimp [R]; linarith)] with t ht
  exact primeOverlapLoss_eq_fixed_sum t R ht.le g
