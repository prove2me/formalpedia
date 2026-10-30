-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_actual_perpetual_esscher_cdf_density_implies_scale_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:16:32.163993+00:00
-- url     : https://prove2.me/submissions/08a78091-b750-4b5b-9713-1f0feff52316

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The genuine perpetual tilted CDF reduces C1 to its continuous local density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hLocalDensity : ∀ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν → 0 < m →
      (∀ x : ℝ, ν (Iic x) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x)) →
      ∃ (a : ℝ) (f : ℝ → ℝ), 0 < a ∧
        ContinuousOn f (Ioi (0 : ℝ)) ∧
        (∀ x : ℝ, 0 < x → IntervalIntegrable f volume a x) ∧
        (∀ x : ℝ, 0 < x → (ν (Iic x)).toReal =
          (ν (Iic a)).toReal + ∫ t in a..x, f t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  obtain ⟨ν, m, hν, hm, _, hScaleCDF⟩ :=
    avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
      X q φ hq hφ hroot W hW
  obtain ⟨a, f, ha, hf, hint, hDensity⟩ :=
    hLocalDensity ν m hν hm hScaleCDF
  apply avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density
    ν W φ m a hm ha f hf hint ?_ hDensity
  intro x hx
  have hWnonneg : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
  have hReal :
      (ν (Iic x)).toReal = m * Real.exp (-(φ * x)) * W x := by
    rw [hScaleCDF x, ENNReal.toReal_ofReal]
    exact mul_nonneg (mul_nonneg hm.le (Real.exp_pos _).le) hWnonneg
  rw [hReal]
  have hExp : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    W x = (1 : ℝ) * W x := by ring
    _ = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by rw [hExp]
    _ = (Real.exp (φ * x) / m) *
          (m * Real.exp (-(φ * x)) * W x) := by
      field_simp [ne_of_gt hm]
