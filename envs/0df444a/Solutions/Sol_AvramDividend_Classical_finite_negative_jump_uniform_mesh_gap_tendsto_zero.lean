-- Prove2me | solution 1 for AvramDividend.Classical.finite_negative_jump_uniform_mesh_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:47:58.097596+00:00
-- url     : https://prove2.me/submissions/b99fcd06-bcbb-4bd1-a551-13ed5881dcdf

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_bounds_nat
import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
import Theorems.Thm_AvramDividend_Classical_finite_activity_uniform_mesh_exp_gap_le_intensity_gap
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology

/-- The finite-activity survival mesh Laplace gap vanishes on refinement. -/
theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto
      (fun N : ℕ =>
        (N : ℝ) *
          (Real.exp (-(T / (N : ℝ) *
            ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν)) -
            Real.exp (-(T / (N : ℝ) *
              (ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 0) := by
  let φ : ℕ → ℝ := fun N =>
    ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν
  let lambdaRate : ℝ := (ν (Iio (0 : ℝ))).toReal
  let f : ℕ → ℝ := fun N =>
    (N : ℝ) *
      (Real.exp (-(T / (N : ℝ) * φ N)) -
        Real.exp (-(T / (N : ℝ) * lambdaRate)))
  have hBounds (N : ℕ) : 0 ≤ φ N ∧ φ N ≤ lambdaRate :=
    finite_negative_jump_exponential_deficit_bounds_nat ν hFinite N
  have hLow (N : ℕ) : 0 ≤ f N := by
    have htime : 0 ≤ T / (N : ℝ) :=
      div_nonneg hT (Nat.cast_nonneg N)
    have hArg : T / (N : ℝ) * φ N ≤ T / (N : ℝ) * lambdaRate :=
      mul_le_mul_of_nonneg_left (hBounds N).2 htime
    have hExp :
        Real.exp (-(T / (N : ℝ) * lambdaRate)) ≤
          Real.exp (-(T / (N : ℝ) * φ N)) :=
      (Real.exp_le_exp).2 (neg_le_neg hArg)
    exact mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.2 hExp)
  have hHigh (N : ℕ) : f N ≤ T * (lambdaRate - φ N) := by
    by_cases hN : N = 0
    · subst N
      have hFzero : f 0 = 0 := by simp [f]
      rw [hFzero]
      exact mul_nonneg hT (sub_nonneg.2 (hBounds 0).2)
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      exact finite_activity_uniform_mesh_exp_gap_le_intensity_gap
        (φ N) lambdaRate T N (hBounds N).1 (hBounds N).2 hT hNpos
  have hφ :
      Tendsto φ atTop (𝓝 lambdaRate) := by
    simpa only [φ, lambdaRate] using
      (finite_negative_jump_exponential_deficit_limit_nat ν hFinite)
  have hTop :
      Tendsto (fun N : ℕ => T * (lambdaRate - φ N)) atTop (𝓝 0) := by
    have hMul :
        Tendsto (fun N : ℕ => T * (lambdaRate - φ N)) atTop
          (𝓝 (T * (lambdaRate - lambdaRate))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub hφ)
    simpa using hMul
  simpa only [f, φ, lambdaRate] using (squeeze_zero hLow hHigh hTop)
