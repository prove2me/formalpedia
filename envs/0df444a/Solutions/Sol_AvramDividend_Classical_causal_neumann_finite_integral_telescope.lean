-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_finite_integral_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:10:07.96726+00:00
-- url     : https://prove2.me/submissions/bb854107-3f18-4f93-b6d7-cfe76df178d7

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Pi
import Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_resolvent_telescope
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_finset_sum

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The finite Neumann telescope for an integrable causal Volterra operator. -/
theorem solution
    (a : ℝ) (B F : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Q i) +
      (fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x,
          B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i s) ∂volume)) =
      F - Q (n + 1) := by
  classical
  let T : (ℝ → ℝ) → (ℝ → ℝ) :=
    fun f x => (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * f s ∂volume)
  have hlin (m : ℕ) :
      T (∑ i ∈ Finset.range (m + 1), Q i) =
        ∑ i ∈ Finset.range (m + 1), T (Q i) := by
    funext x
    simp only [T, Finset.sum_apply]
    rw [causal_Ioc_kernel_integral_finset_sum B Q x m (hI m x)]
    rw [Finset.mul_sum]
  have hrec (m : ℕ) : Q (m + 1) = -T (Q m) := hstep m
  simpa only [T, Finset.sum_apply] using
    (causal_neumann_finite_resolvent_telescope F T Q hzero hrec hlin n)
