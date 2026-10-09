-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:20:35.267981+00:00
-- url     : https://prove2.me/submissions/4fe2fa3a-1553-4143-af6f-d66fd3791917

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_positive_magnitude_compensator_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_discounted_moment_integrable
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_nonneg
import Theorems.Thm_AvramDividend_Classical_esscher_nnreal_jump_mass_lt_drift_of_positive_root

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
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Integrable
        (fun z : ℝ≥0 => (z : ℝ) * Real.exp (-(φ * (z : ℝ))))
        (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) ∧
      (∫ z : ℝ≥0,
        (z : ℝ) * Real.exp (-(φ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) < X.drift := by
  let νp : Measure ℝ≥0 :=
    X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  have hExp : IntegrableOn
      (fun y : ℝ => Real.exp (φ * y) - 1) (Iio (0 : ℝ)) X.ν :=
    bv_exponential_jump_integrable_nonneg X hbv φ hφ.le
  have hnegf :
      (fun y : ℝ => 1 - Real.exp (φ * y)) =
        -(fun y : ℝ => Real.exp (φ * y) - 1) := by
    funext y
    change 1 - Real.exp (φ * y) = -(Real.exp (φ * y) - 1)
    ring
  have hNeg : IntegrableOn
      (fun y : ℝ => 1 - Real.exp (φ * y)) (Iio (0 : ℝ)) X.ν := by
    rw [hnegf]
    exact hExp.neg
  have hJ : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ)))) νp :=
    positive_magnitude_compensator_integrable X.ν φ hNeg
  have hA : Integrable
      (fun z : ℝ≥0 => (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) νp :=
    esscher_discounted_moment_integrable νp φ hφ hJ
  have hψ :=
    bv_laplace_exponent_positive_magnitude_nonneg X hbv φ hφ.le
  have hroot' : X.drift * φ -
      (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂νp) = q := by
    simpa only [neg_mul] using hψ.symm.trans hroot
  have hsubcritical :=
    esscher_nnreal_jump_mass_lt_drift_of_positive_root
      νp X.drift φ q hφ hq hA hJ hroot'
  exact ⟨hA, hsubcritical⟩
