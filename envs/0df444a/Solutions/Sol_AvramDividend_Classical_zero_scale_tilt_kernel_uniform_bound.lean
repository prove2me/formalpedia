-- Prove2me | solution 1 for AvramDividend.Classical.zero_scale_tilt_kernel_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:40:55.86716+00:00
-- url     : https://prove2.me/submissions/41f9c72a-f67f-41d8-974b-f322f9152fe5

import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive scalar multiple of an exponentially weighted zero-scale function is bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ) :
    BddAbove (Set.range (fun x : ℝ =>
      ‖q * (Real.exp (-(θ * x)) * W₀ x)‖)) := by
  obtain ⟨B, hB⟩ :=
    scaleFunction_global_weighted_norm_bddAbove
      X 0 W₀ hW₀ θ hθ hψ
  refine ⟨q * B, ?_⟩
  rintro z ⟨x, rfl⟩
  have hx : ‖Real.exp (-(θ * x)) * W₀ x‖ ≤ B := hB ⟨x, rfl⟩
  calc
    ‖q * (Real.exp (-(θ * x)) * W₀ x)‖ =
        q * ‖Real.exp (-(θ * x)) * W₀ x‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hq]
    _ ≤ q * B := mul_le_mul_of_nonneg_left hx hq
