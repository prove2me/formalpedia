-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:51:49.987582+00:00
-- url     : https://prove2.me/submissions/062617e4-8f0c-4cb1-b65e-7eff6a4b14b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_void_indicator_past_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Real probability factorisation of original intrinsic future voids:
every raw-measurable source-past event is independent of a future mark void. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Ω) (hApast : MeasurableSet[𝓕 s] A)
    (hAraw : MeasurableSet A) :
    P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0}) =
    P A * P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0} := by
  let V : Set Ω := {ω : Ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0}
  have hVm : MeasurableSet V :=
    avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
      X s t hst B hB
  have hFactor :=
    avram_wave7_06_original_intrinsic_future_void_indicator_past_factor
      X s t hst B hB A hApast
  change (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω *
    (if ω ∈ V then (1 : ℝ≥0∞) else 0) ∂P) =
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) *
    (∫⁻ ω, if ω ∈ V then (1 : ℝ≥0∞) else 0 ∂P) at hFactor
  have hProd : (fun ω : Ω =>
    A.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (if ω ∈ V then (1 : ℝ≥0∞) else 0)) =
      (A ∩ V).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hv : ω ∈ V <;>
      simp [Set.indicator, ha, hv]
  change P (A ∩ V) = P A * P V
  calc
    P (A ∩ V) =
        ∫⁻ ω, (A ∩ V).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P :=
      (lintegral_indicator_one (hAraw.inter hVm)).symm
    _ = ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (if ω ∈ V then (1 : ℝ≥0∞) else 0) ∂P := by
          rw [hProd]
    _ = (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) *
        (∫⁻ ω, if ω ∈ V then (1 : ℝ≥0∞) else 0 ∂P) := hFactor
    _ = P A * P V := by
      have hAint :
          (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) = P A :=
        lintegral_indicator_one hAraw
      have hVint :
          (∫⁻ ω, if ω ∈ V then (1 : ℝ≥0∞) else 0 ∂P) = P V := by
        calc
          (∫⁻ ω, if ω ∈ V then (1 : ℝ≥0∞) else 0 ∂P) =
              (∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) := by
                apply lintegral_congr
                intro ω
                by_cases hv : ω ∈ V <;> simp [Set.indicator, hv]
          _ = P V := lintegral_indicator_one hVm
      rw [hAint, hVint]
