-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_shifted_negative_band_indicator_integral_eq_event_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:04:36.079872+00:00
-- url     : https://prove2.me/submissions/6dcf80c6-1d6e-4ec0-8f65-ad9051e29d62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- An actual shifted negative-band cell indicator integrates to its event probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    (let E : Set Ω := {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}
     (∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂P) = P E) := by
  classical
  let E : Set Ω := {ω : Ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}
  have hZero : MeasurableSet {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} :=
    avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
      X s (s + T) (by simp) _ (by measurability)
  have hE : MeasurableSet E := by
    simpa [E, Set.compl_setOf] using hZero.compl
  change (∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂P) = P E
  have hOne : (1 : Ω → ENNReal) = (fun _ : Ω => (1 : ENNReal)) := by
    funext ω
    rfl
  have hInt := lintegral_indicator_one (μ := P) hE
  rw [hOne] at hInt
  exact hInt
