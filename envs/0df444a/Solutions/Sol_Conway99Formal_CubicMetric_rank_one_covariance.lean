-- Prove2me | solution 1 for Conway99Formal.CubicMetric.rank_one_covariance
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:56:15.38717+00:00
-- url     : https://prove2.me/submissions/9394b185-feba-4c87-a8dc-6f96f28b4f96

import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

namespace Conway99Formal.CubicMetric












end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

open Conway99Formal.CubicMetric in
theorem solution {U T I : Type*} [Fintype U] [Fintype T]
    [Fintype I] [DecidableEq I] (tau : T → I → ℝ) (h : U → T → ℝ)
    (F : U → Matrix I I ℝ)
    (hF : ∀ u i j, F u i j = -(∑ t, h u t * tau t i * tau t j) / 3)
    (hpair : ∀ t s,
      (∑ u, h u t * h u s) = 63 * (∑ k, tau t k * tau s k)) :
    (∑ u, F u * F u) =
      (7 : ℝ) • Matrix.of (fun i j =>
        ∑ t, ∑ s, (∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j) := by
  classical
  have hsq (u : U) (i j : I) :
      9 * (F u * F u) i j =
        ∑ t, ∑ s,
          h u t * h u s * (∑ k, tau t k * tau s k) * tau t i * tau s j := by
    calc
      9 * (F u * F u) i j =
          ∑ k, (∑ t, h u t * tau t i * tau t k) *
            (∑ s, h u s * tau s k * tau s j) := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [hF u i k, hF u k j]
        ring
      _ = ∑ k, ∑ t, ∑ s,
            (h u t * tau t i * tau t k) *
              (h u s * tau s k * tau s j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul_sum]
      _ = ∑ t, ∑ s, ∑ k,
            (h u t * tau t i * tau t k) *
              (h u s * tau s k * tau s j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_comm]
      _ = ∑ t, ∑ s,
            h u t * h u s * (∑ k, tau t k * tau s k) * tau t i * tau s j := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s _
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have hsum :
      9 * (∑ u, (F u * F u) i j) =
        ∑ t, ∑ s,
          (∑ u, h u t * h u s) *
            (∑ k, tau t k * tau s k) * tau t i * tau s j := by
    calc
      9 * (∑ u, (F u * F u) i j) =
          ∑ u, 9 * (F u * F u) i j := by rw [Finset.mul_sum]
      _ = ∑ u, ∑ t, ∑ s,
            h u t * h u s * (∑ k, tau t k * tau s k) * tau t i * tau s j := by
        apply Finset.sum_congr rfl
        intro u _
        exact hsq u i j
      _ = ∑ t, ∑ s, ∑ u,
            h u t * h u s * (∑ k, tau t k * tau s k) * tau t i * tau s j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_comm]
      _ = ∑ t, ∑ s,
            (∑ u, h u t * h u s) *
              (∑ k, tau t k * tau s k) * tau t i * tau s j := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s _
        simp only [Finset.sum_mul]
  have hscaled :
      9 * (∑ u, (F u * F u) i j) =
        9 * (7 * (∑ t, ∑ s,
          (∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j)) := by
    calc
      9 * (∑ u, (F u * F u) i j) =
          ∑ t, ∑ s,
            (∑ u, h u t * h u s) *
              (∑ k, tau t k * tau s k) * tau t i * tau s j := hsum
      _ = ∑ t, ∑ s,
            63 * (∑ k, tau t k * tau s k) *
              (∑ k, tau t k * tau s k) * tau t i * tau s j := by
        simp_rw [hpair]
      _ = 63 * (∑ t, ∑ s,
            (∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j) := by
        calc
          ∑ t, ∑ s,
              63 * (∑ k, tau t k * tau s k) *
                (∑ k, tau t k * tau s k) * tau t i * tau s j =
            ∑ t, ∑ s,
              63 * ((∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j) := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = 63 * (∑ t, ∑ s,
                (∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.mul_sum]
      _ = 9 * (7 * (∑ t, ∑ s,
            (∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j)) := by ring
  nlinarith [hscaled]
