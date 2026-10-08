-- Prove2me | solution 1 for ConnesGreen.prime_convolution_zero_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:46:54.526051+00:00
-- url     : https://prove2.me/submissions/c6da08e0-379b-4c9c-9a34-53fb4b78f9a0

import Theorems.Thm_ConnesGreen_convolution_overlap_dirichlet_energy_bound
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
theorem solution (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) (hT : 2 * T ≤ Real.log 2) :
    primeSum (conv g (starInv g)) = 0 := by
  have hz : ∀ x : ℝ, 2 * T ≤ |x| → conv g (starInv g) x = 0 := by
    intro x hx
    have hb := convolution_overlap_dirichlet_energy_bound T g hg x
    rw [max_eq_right (by linarith : 2 * T - |x| ≤ 0), mul_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  have hall : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n)) = 0 := by
    intro n
    by_cases hn : n < 2
    · interval_cases n <;> simp
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt hn)
      have hl : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
      have hl0 : 0 ≤ Real.log (n : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hl
      have hp : conv g (starInv g) (Real.log n) = 0 :=
        hz _ (by rw [abs_of_nonneg hl0]; exact hT.trans hl)
      have hm : conv g (starInv g) (-Real.log n) = 0 :=
        hz _ (by rw [abs_neg, abs_of_nonneg hl0]; exact hT.trans hl)
      simp [hp, hm]
  unfold primeSum
  simp only [hall, tsum_zero]
