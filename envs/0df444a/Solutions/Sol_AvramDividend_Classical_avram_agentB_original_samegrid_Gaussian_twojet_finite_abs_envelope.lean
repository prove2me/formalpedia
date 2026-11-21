-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:08:58.393998+00:00
-- url     : https://prove2.me/submissions/907429ca-06c8-47d2-afaf-e1182da905ed

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
open BigOperators
noncomputable section
set_option autoImplicit false

/-- Finite-cell original Gaussian two-jet pre/post coefficient
difference is bounded by absolute cellwise gradient and Hessian errors. -/
theorem solution
    (n : ℕ) (e z u a b c d : ℕ → ℝ) :
    |∑ i ∈ Finset.range n, e i *
      ((a i * z i + b i * u i) - (c i * z i + d i * u i))| ≤
      ∑ i ∈ Finset.range n, |e i| *
        (|a i - c i| * |z i| + |b i - d i| * |u i|) := by
  calc
    |∑ i ∈ Finset.range n, e i *
        ((a i * z i + b i * u i) - (c i * z i + d i * u i))| ≤
      ∑ i ∈ Finset.range n,
        |e i * ((a i * z i + b i * u i) - (c i * z i + d i * u i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, |e i| *
        (|a i - c i| * |z i| + |b i - d i| * |u i|) := by
      apply Finset.sum_le_sum
      intro i hi
      have hEq :
          ((a i * z i + b i * u i) - (c i * z i + d i * u i)) =
            (a i - c i) * z i + (b i - d i) * u i := by ring
      rw [hEq, abs_mul]
      apply mul_le_mul_of_nonneg_left
      · calc
          |(a i - c i) * z i + (b i - d i) * u i| ≤
            |(a i - c i) * z i| + |(b i - d i) * u i| := abs_add_le _ _
          _ = |a i - c i| * |z i| + |b i - d i| * |u i| := by rw [abs_mul, abs_mul]
      · exact abs_nonneg _
