-- Prove2me | solution 1 for AvramDividend.Classical.avram_a29_original_positive_sigma_intrinsic_gaussian_exact_laplace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:11:09.722206+00:00
-- url     : https://prove2.me/submissions/503c59a8-a613-4610-8103-01efcefa9d59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original positive-sigma intrinsic Gaussian Laplace law follows from its genuine physical centred normal distribution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by
  have hLaw :=
    avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
      X hX hFinite hPositive R hR G hEq
  intro t θ _
  let v : ℝ≥0 := NNReal.mk ((t : ℝ) * X.σ ^ 2)
    (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))
  have hGLaw : HasLaw (G t) (gaussianReal 0 v) P := hLaw t
  obtain ⟨hInt, hMoment⟩ :=
    avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
      (G t) v hGLaw θ
  refine ⟨hInt, ?_⟩
  calc
    (∫ ω, Real.exp (θ * G t ω) ∂P) =
      Real.exp ((v : ℝ) * θ ^ 2 / 2) := hMoment
    _ = Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by
      rw [laplaceExponent_zero_jump_measure]
      congr 1
      dsimp [v]
      ring
