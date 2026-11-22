-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_actual_simple_negative_mark_countable_stop_mean_zero_unconditional_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:51:51.251195+00:00
-- url     : https://prove2.me/submissions/514382b5-3259-4fb0-9ba1-21b6fe1cde6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_finite_simple_negative_mark_rightCont_martingale_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false


/-- Optional stopping for the true physical finite-simple negative mark process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)
    Integrable (stoppedValue F τ) P ∧
      (∫ ω, stoppedValue F τ ω ∂P) = 0 := by
  classical
  intro NX B F
  have hMart : Martingale F 𝓕.rightCont P := by
    simpa only [F, B, NX] using
      (avram_oai_original_physical_finite_simple_negative_mark_rightCont_martingale_allactivity_20261122
        X S hS hNeg hν g)
  have hStop :=
    avram_lsv_finite_grid_stopped_martingale_expectation
      P 𝓕.rightCont F hMart T τ hτ hτbound hτcount
  have hF0 : ∀ ω, F 0 ω = 0 := by
    intro ω
    simp [F]
  have hMean : (∫ ω, F T ω ∂P) = 0 := by
    have hEQ := hMart.setIntegral_eq (i := (0 : ℝ≥0)) (j := T)
      (by exact bot_le) (s := Set.univ) (by simp)
    have hGlobal : (∫ ω, F 0 ω ∂P) = (∫ ω, F T ω ∂P) := by
      simpa only [MeasureTheory.setIntegral_univ] using hEQ
    calc
      (∫ ω, F T ω ∂P) = (∫ ω, F 0 ω ∂P) := hGlobal.symm
      _ = 0 := by simp [hF0]
  exact ⟨hStop.1, hStop.2.trans hMean⟩
