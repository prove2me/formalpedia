-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_hjb_diff_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:42:03.575299+00:00
-- url     : https://prove2.me/submissions/56010ae6-c7e3-4562-a709-ebc56b1ee4d7

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The exact original-generator HJB estimate gives an ODE upper comparison. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q jumpRate W β ε y : ℝ)
    (hA : 0 < X.σ ^ 2 / 2)
    (hJump : -jumpRate * w y ≤
      ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν)
    (hHJB : X.generator w y - q * w y ≤ 0)
    (hUpper : w y ≤ W) (hQLambda : 0 ≤ q + jumpRate)
    (hBeta : -X.c ≤ (X.σ ^ 2 / 2) * β)
    (hEps : (q + jumpRate) * W ≤ (X.σ ^ 2 / 2) * ε)
    (hDeriv : 0 ≤ deriv w y) :
    iteratedDeriv 2 w y ≤ β * deriv w y + ε := by
  let a : ℝ := X.σ ^ 2 / 2
  have hW : (q + jumpRate) * w y ≤ (q + jumpRate) * W :=
    mul_le_mul_of_nonneg_left hUpper hQLambda
  have hBase : a * iteratedDeriv 2 w y + X.c * deriv w y ≤
      (q + jumpRate) * w y := by
    dsimp [SpectrallyNegativeLevy.generator] at hHJB
    dsimp [a]
    linarith [hJump]
  have hC : -X.c * deriv w y ≤ a * β * deriv w y := by
    exact mul_le_mul_of_nonneg_right hBeta hDeriv
  have hBound : a * iteratedDeriv 2 w y ≤
      a * (β * deriv w y + ε) := by
    calc
      a * iteratedDeriv 2 w y ≤
          (q + jumpRate) * w y - X.c * deriv w y := by linarith [hBase]
      _ ≤ (q + jumpRate) * W - X.c * deriv w y := by linarith [hW]
      _ ≤ a * ε + a * β * deriv w y := by
        calc
          (q + jumpRate) * W - X.c * deriv w y =
              (q + jumpRate) * W + (-X.c * deriv w y) := by ring
          _ ≤ a * ε + (a * β * deriv w y) := add_le_add hEps hC
          _ = a * ε + a * β * deriv w y := rfl
      _ = a * (β * deriv w y + ε) := by ring
  exact le_of_mul_le_mul_left hBound hA
