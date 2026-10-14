-- Prove2me | solution 1 for DbarRegularity.dist_le_of_mem_closedCube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:51:47.808979+00:00
-- url     : https://prove2.me/submissions/fb7cc0f0-b33e-4ab3-8a17-ea637fa5693f

import Definitions.Def_DbarRegularity_Setting



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem dist_le_of_mem_closedCube {d : ℕ} {a x y : EuclideanSpace ℝ (Fin d)} {s : ℝ}
    (hx : x ∈ closedCube a s) (hy : y ∈ closedCube a s) : dist y x ≤ Real.sqrt d * s := by
  have hc : ∀ i, dist (y i) (x i) ^ 2 ≤ s ^ 2 := by
    intro i
    have h1 := hx i; have h2 := hy i
    rw [Real.dist_eq, sq_abs]
    nlinarith
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (y i) (x i) ^ 2) ≤ Real.sqrt (∑ _i : Fin d, s ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hc i)
    _ = Real.sqrt d * s := by
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · simp
        · have hs : 0 ≤ s := by
            have h1 := hx ⟨0, hd⟩; linarith
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs]

end DbarRegularity

open DbarRegularity

theorem solution {d : ℕ} {a x y : EuclideanSpace ℝ (Fin d)} {s : ℝ}
    (hx : x ∈ closedCube a s) (hy : y ∈ closedCube a s) : dist y x ≤ Real.sqrt d * s :=
  dist_le_of_mem_closedCube hx hy
