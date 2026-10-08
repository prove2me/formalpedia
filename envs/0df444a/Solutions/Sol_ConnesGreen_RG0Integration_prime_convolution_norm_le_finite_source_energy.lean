-- Prove2me | solution 1 for ConnesGreen.RG0Integration.prime_convolution_norm_le_finite_source_energy
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:39:17.233856+00:00
-- url     : https://prove2.me/submissions/b31e443f-84dc-43be-ab30-fee0af0f59bd

import Theorems.Thm_ConnesGreen_prime_convolution_hasSum_exp_cutoff
import Theorems.Thm_ConnesGreen_convolution_overlap_dirichlet_energy_bound
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section


theorem solution (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (N : ℕ) (hN : Real.exp (2*t) < N) :
    ‖primeSum (conv g (starInv g))‖ ≤
      4 * ‖sourceEmbed t (problemOneL g)‖ ^ 2 *
        ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          max (2*t - |Real.log n|) 0 := by
  have he := actual_physical_test_norm t ht g hg
  have hb : ∀ x : ℝ, ‖conv g (starInv g) x‖ ≤
      2 * ‖sourceEmbed t (problemOneL g)‖ ^ 2 * max (2*t - |x|) 0 := by
    intro x
    rw [he]
    exact convolution_overlap_dirichlet_energy_bound t g hg x
  have hp := (prime_convolution_hasSum_exp_cutoff t g hg N hN).tsum_eq
  change ‖∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n))‖ ≤ _
  rw [hp]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, 4 * ‖sourceEmbed t (problemOneL g)‖ ^ 2 *
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n) * max (2*t - |Real.log n|) 0) := by
      apply Finset.sum_le_sum
      intro n _
      have hw : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
        div_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      have h := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (hb (Real.log n)) (hb (-Real.log n)))) hw
      simp only [abs_neg] at h
      nlinarith
    _ = _ := by rw [Finset.mul_sum]
