-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:15.932206+00:00
-- url     : https://prove2.me/submissions/feb302dc-c9b2-4ca4-a4c5-bee17b4adab2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a48_positive_exponential_tail_chernoff_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a60_original_zerojump_gaussian_centered_increment_positive_mgf_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact positive Gaussian Chernoff bound on an original drift-centred physical source increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ r δ : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r) :
    let Z : Ω → ℝ := fun ω =>
      ((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
    Integrable (fun ω => if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) P →
    Integrable (fun ω => Real.exp ((θ + r) * Z ω)) P →
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (-r * δ + ((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2) := by
  let Z : Ω → ℝ := fun ω =>
    ((X.X t ω - X.X s ω) -
      ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
  change Integrable (fun ω => if δ ≤ Z ω then
      Real.exp (θ * Z ω) else 0) P →
    Integrable (fun ω => Real.exp ((θ + r) * Z ω)) P →
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (-r * δ + ((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2)
  intro hEventI hExpI
  have hpt (ω : Ω) :
      (if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) ≤
      Real.exp (-r * δ) * Real.exp ((θ + r) * Z ω) :=
    avram_ga_a48_positive_exponential_tail_chernoff_majorant
      (Z ω) θ r δ hr
  have htheta : 0 ≤ θ + r := add_nonneg hθ hr
  calc
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
        (∫ ω, Real.exp (-r * δ) *
          Real.exp ((θ + r) * Z ω) ∂P) :=
      integral_mono hEventI (hExpI.const_mul _) hpt
    _ = Real.exp (-r * δ) *
        (∫ ω, Real.exp ((θ + r) * Z ω) ∂P) := by
      rw [integral_const_mul]
    _ = Real.exp (-r * δ) *
        Real.exp (((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2) := by
      rw [show (∫ ω, Real.exp ((θ + r) * Z ω) ∂P) =
        Real.exp (((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2) from
        avram_ga_a60_original_zerojump_gaussian_centered_increment_positive_mgf_exact
          X hν hσ s t hst (θ + r) htheta]
    _ = Real.exp (-r * δ + ((t - s : ℝ≥0) : ℝ) *
          (θ + r)^2 / 2) := (Real.exp_add _ _).symm
