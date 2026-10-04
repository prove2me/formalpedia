-- Prove2me | solution 1 for Conway99Formal.CubicMetric.rank_one_trace_product
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:56:16.076671+00:00
-- url     : https://prove2.me/submissions/65c74c63-a924-40f1-9637-801875c189e8

import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

namespace Conway99Formal.CubicMetric

private theorem four_sum_swap {I T : Type*} [Fintype I] [Fintype T]
    (f : I → I → T → T → ℝ) :
    (∑ i, ∑ j, ∑ t, ∑ u, f i j t u) =
      ∑ t, ∑ u, ∑ i, ∑ j, f i j t u := by
  classical
  calc
    (∑ i, ∑ j, ∑ t, ∑ u, f i j t u) =
        ∑ i, ∑ t, ∑ j, ∑ u, f i j t u := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ t, ∑ i, ∑ j, ∑ u, f i j t u := by rw [Finset.sum_comm]
    _ = ∑ t, ∑ i, ∑ u, ∑ j, f i j t u := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ t, ∑ u, ∑ i, ∑ j, f i j t u := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_comm]










end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

open Conway99Formal.CubicMetric in
theorem solution {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq I] (tau : T → I → ℝ) (a b : T → ℝ)
    (F H : Matrix I I ℝ)
    (hF : ∀ i j, F i j = -(∑ t, a t * tau t i * tau t j) / 3)
    (hH : ∀ i j, H i j = -(∑ t, b t * tau t i * tau t j) / 3) :
    9 * Matrix.trace (F * H) =
      ∑ t, ∑ u, a t * (∑ i, tau t i * tau u i) ^ 2 * b u := by
  classical
  have htrace : Matrix.trace (F * H) = ∑ i, ∑ j, F i j * H j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have hscaled :
      9 * Matrix.trace (F * H) =
        ∑ i, ∑ j,
          (∑ t, a t * tau t i * tau t j) *
            (∑ u, b u * tau u j * tau u i) := by
    rw [htrace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hF i j, hH j i]
    ring
  calc
    9 * Matrix.trace (F * H) =
        ∑ i, ∑ j,
          (∑ t, a t * tau t i * tau t j) *
            (∑ u, b u * tau u j * tau u i) := hscaled
    _ = ∑ i, ∑ j, ∑ t, ∑ u,
          a t * tau t i * tau t j * (b u * tau u j * tau u i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul_sum]
    _ = ∑ t, ∑ u, ∑ i, ∑ j,
          a t * tau t i * tau t j * (b u * tau u j * tau u i) :=
      four_sum_swap _
    _ = ∑ t, ∑ u, a t * (∑ i, tau t i * tau u i) ^ 2 * b u := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
