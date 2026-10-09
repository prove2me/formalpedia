-- Prove2me | solution 1 for GaussianMatrix.sMin_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:06:37.570665+00:00
-- url     : https://prove2.me/submissions/06ac8ba9-0bdf-4f78-a616-1061e6a3efbe

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_sMin_le_imp_dist_le
import Theorems.Thm_GaussianMatrix_dist_col_span_small_ball

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (s : ℝ) (hs : 0 ≤ s)
    (hsd : n * s ^ 2 ≤ (N : ℝ) - n + 1) :
    (gaussianMatrix N n) {A | sMin (Matrix.of A) ≤ s}
      ≤ ENNReal.ofReal (n * (Real.exp 1 * n * s ^ 2 / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by
  set D : Fin n → (Fin N → Fin n → ℝ) → ℝ := fun j A =>
    ⨅ x : {x : Fin n → ℝ // x j = 1},
      Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1)) with hD
  have hD0 : ∀ j A, 0 ≤ D j A := fun j A =>
    Real.iInf_nonneg fun x => Real.sqrt_nonneg _
  have hsub : {A : Fin N → Fin n → ℝ | sMin (Matrix.of A) ≤ s}
      ⊆ ⋃ j : Fin n, {A | D j A ^ 2 ≤ n * s ^ 2} := by
    intro A hA
    obtain ⟨j, hj⟩ := sMin_le_imp_dist_le hn (Matrix.of A) s hA
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    show D j A ^ 2 ≤ n * s ^ 2
    have h1 : D j A ^ 2 ≤ (Real.sqrt n * s) ^ 2 := pow_le_pow_left₀ (hD0 j A) hj 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at h1
  have hu0 : 0 ≤ (n : ℝ) * s ^ 2 := by positivity
  calc (gaussianMatrix N n) {A | sMin (Matrix.of A) ≤ s}
      ≤ (gaussianMatrix N n) (⋃ j : Fin n, {A | D j A ^ 2 ≤ n * s ^ 2}) := measure_mono hsub
    _ ≤ ∑ j : Fin n, (gaussianMatrix N n) {A | D j A ^ 2 ≤ n * s ^ 2} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal
          ((Real.exp 1 * (n * s ^ 2) / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) :=
        Finset.sum_le_sum fun j _ => dist_col_span_small_ball hnN j (n * s ^ 2) hu0 hsd
    _ = ENNReal.ofReal
          (n * (Real.exp 1 * n * s ^ 2 / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, mul_assoc]
