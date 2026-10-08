-- Prove2me | solution 1 for AvramDividend.Classical.psi_continuousOn_Icc_of_compensated_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:29:42.542006+00:00
-- url     : https://prove2.me/submissions/7718323f-f255-4d5a-93a3-de473bc79dd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_continuousOn_lintegral_parameter_dominated_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A local common compensated-jump envelope forces continuity of source ψ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : ℝ) (hB : 0 ≤ B)
    (bound : ℝ → ℝ)
    (hboundInt : Integrable bound (X.ν.restrict (Iio (0 : ℝ))))
    (hdom : ∀ θ ∈ Icc (0 : ℝ) B,
      ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))),
        ‖Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y‖ ≤ bound y) :
    ContinuousOn X.ψ (Icc (0 : ℝ) B) := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun θ y =>
    Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y
  have hmeas : ∀ θ ∈ Icc (0 : ℝ) B, AEStronglyMeasurable (F θ) μ := by
    intro θ hθ
    have hexp : Measurable (fun y : ℝ => Real.exp (θ * y)) := by
      fun_prop
    have hlin : Measurable (fun y : ℝ => θ * y) := by
      fun_prop
    have hind : Measurable (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y) := by
      exact measurable_const.indicator measurableSet_Ioo
    have hm : Measurable (F θ) := by
      change Measurable (fun y : ℝ => Real.exp (θ * y) - 1 -
        (θ * y) * (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y)
      exact (hexp.sub measurable_const).sub (hlin.mul hind)
    exact hm.aestronglyMeasurable
  have hpoint : ∀ᵐ y : ℝ ∂μ,
      Continuous (fun z : Icc (0 : ℝ) B => F z.1 y) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp [F]
    fun_prop
  have hInt : ContinuousOn (fun θ : ℝ => ∫ y : ℝ, F θ y ∂μ)
      (Icc (0 : ℝ) B) :=
    continuousOn_lintegral_parameter_dominated_Icc
      μ 0 B F bound hmeas hdom hboundInt hpoint
  have hpoly : Continuous (fun θ : ℝ =>
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2) := by
    fun_prop
  change ContinuousOn (fun θ : ℝ =>
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      ∫ y : ℝ, F θ y ∂μ) (Icc (0 : ℝ) B)
  exact hpoly.continuousOn.add hInt
