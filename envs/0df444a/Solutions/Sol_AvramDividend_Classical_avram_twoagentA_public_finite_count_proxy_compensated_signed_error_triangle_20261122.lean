-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_finite_count_proxy_compensated_signed_error_triangle_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:06:40.321197+00:00
-- url     : https://prove2.me/submissions/cb2fa352-3f3c-46d7-86e0-dd3a70f7462d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (S : Finset ℕ) (c δ N rate : ℕ → ℝ) (U V T : ℝ)
    (hT : 0 ≤ T)
    (hRandom : |U - ∑ i ∈ S, c i * N i| ≤ ∑ i ∈ S, δ i * N i)
    (hDrift : |V - ∑ i ∈ S, c i * rate i| ≤ ∑ i ∈ S, δ i * rate i) :
    |(U - T * V) -
      ∑ i ∈ S, c i * (N i - T * rate i)| ≤
      ∑ i ∈ S, δ i * (N i + T * rate i) := by
  classical
  have hSum :
      (∑ i ∈ S, c i * (N i - T * rate i)) =
        (∑ i ∈ S, c i * N i) - T * (∑ i ∈ S, c i * rate i) := by
    calc
      (∑ i ∈ S, c i * (N i - T * rate i)) =
          (∑ i ∈ S, c i * N i) -
          (∑ i ∈ S, c i * (T * rate i)) := by
            simp [mul_sub, Finset.sum_sub_distrib]
      _ = (∑ i ∈ S, c i * N i) -
          T * (∑ i ∈ S, c i * rate i) := by
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (by intro i hi; ring)
  have hEq :
      (U - T * V) - ∑ i ∈ S, c i * (N i - T * rate i) =
        (U - ∑ i ∈ S, c i * N i) -
        T * (V - ∑ i ∈ S, c i * rate i) := by
    rw [hSum]
    ring
  rw [hEq]
  calc
    |(U - ∑ i ∈ S, c i * N i) -
      T * (V - ∑ i ∈ S, c i * rate i)| ≤
        |U - ∑ i ∈ S, c i * N i| +
        |T * (V - ∑ i ∈ S, c i * rate i)| := by
          simpa using
            (abs_sub_le (U - ∑ i ∈ S, c i * N i) (0 : ℝ)
              (T * (V - ∑ i ∈ S, c i * rate i)))
    _ = |U - ∑ i ∈ S, c i * N i| +
        T * |V - ∑ i ∈ S, c i * rate i| := by
          rw [abs_mul, abs_of_nonneg hT]
    _ ≤ (∑ i ∈ S, δ i * N i) +
        T * (∑ i ∈ S, δ i * rate i) :=
          add_le_add hRandom (mul_le_mul_of_nonneg_left hDrift hT)
    _ = ∑ i ∈ S, δ i * (N i + T * rate i) := by
          simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            mul_assoc, mul_comm, mul_left_comm]
