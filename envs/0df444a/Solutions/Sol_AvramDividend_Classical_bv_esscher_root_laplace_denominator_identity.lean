-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_laplace_denominator_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:39:18.711251+00:00
-- url     : https://prove2.me/submissions/2af6f36b-75f8-42e4-bc0d-d8e0a6ea81f0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_positive_magnitude_compensator_integrable
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_nonneg
import Theorems.Thm_AvramDividend_Classical_esscher_jump_compensator_difference_integral
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ s : ℝ) (hφ : 0 < φ) (hs : 0 < s)
    (hroot : X.ψ φ = q) :
    X.ψ (φ + s) - q =
      X.drift * s -
        (∫ z : ℝ≥0,
          Real.exp (-(φ * (z : ℝ))) *
            (1 - Real.exp (-(s * (z : ℝ))))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) := by
  let μ : Measure ℝ≥0 :=
    X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  have hφnonneg : 0 ≤ φ := hφ.le
  have hφs : 0 ≤ φ + s := by linarith
  have hnegComp (θ : ℝ) (hθ : 0 ≤ θ) :
      IntegrableOn
        (fun y : ℝ => 1 - Real.exp (θ * y)) (Iio (0 : ℝ)) X.ν := by
    have hneg :=
      (bv_exponential_jump_integrable_nonneg X hbv θ hθ).neg
    have heq : EqOn
        (-(fun y : ℝ => Real.exp (θ * y) - 1))
        (fun y : ℝ => 1 - Real.exp (θ * y))
        (Iio (0 : ℝ)) := by
      intro y hy
      change -(Real.exp (θ * y) - 1) = 1 - Real.exp (θ * y)
      ring
    exact (integrableOn_congr_fun heq measurableSet_Iio).mp hneg
  have hJφ : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ)))) μ :=
    positive_magnitude_compensator_integrable X.ν φ
      (hnegComp φ hφnonneg)
  have hJplus : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-((φ + s) * (z : ℝ)))) μ :=
    positive_magnitude_compensator_integrable X.ν (φ + s)
      (hnegComp (φ + s) hφs)
  have hdiff :=
    esscher_jump_compensator_difference_integral μ φ s hJφ hJplus
  have hpsiφ :=
    bv_laplace_exponent_positive_magnitude_nonneg X hbv φ hφnonneg
  have hpsiplus :=
    bv_laplace_exponent_positive_magnitude_nonneg X hbv (φ + s) hφs
  simp only [neg_mul] at hpsiφ hpsiplus
  change X.ψ (φ + s) - q =
    X.drift * s -
      (∫ z : ℝ≥0, Real.exp (-(φ * (z : ℝ))) *
          (1 - Real.exp (-(s * (z : ℝ)))) ∂μ)
  calc
    X.ψ (φ + s) - q = X.ψ (φ + s) - X.ψ φ := by rw [hroot]
    _ = (X.drift * (φ + s) -
        (∫ z : ℝ≥0, 1 - Real.exp (-((φ + s) * (z : ℝ))) ∂μ)) -
        (X.drift * φ -
        (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂μ)) := by
          rw [hpsiplus, hpsiφ]
    _ = X.drift * s -
        ((∫ z : ℝ≥0, 1 - Real.exp (-((φ + s) * (z : ℝ))) ∂μ) -
        (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂μ)) := by ring
    _ = X.drift * s -
        (∫ z : ℝ≥0, Real.exp (-(φ * (z : ℝ))) *
            (1 - Real.exp (-(s * (z : ℝ)))) ∂μ) := by rw [hdiff]
