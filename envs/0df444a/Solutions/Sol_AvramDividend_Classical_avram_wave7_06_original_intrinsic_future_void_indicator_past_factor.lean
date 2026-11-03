-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_void_indicator_past_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:18:36.842214+00:00
-- url     : https://prove2.me/submissions/35e9fc1c-32ac-4488-9826-cc1d4778d337

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The future original-path intrinsic marked-jump void indicator factors
from any original-past event, without an auxiliary jump process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω, (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
      (if ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0 then (1 : ℝ≥0∞) else 0) ∂P) =
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) *
    (∫⁻ ω, (if ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0 then (1 : ℝ≥0∞) else 0) ∂P) := by
  obtain ⟨F, hFm, hFrep⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  let H : Ω → ℝ≥0∞ := A.indicator (fun _ => 1)
  let V : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun path =>
    if F path = 0 then 1 else 0
  have hHm : Measurable[𝓕 s] H := measurable_const.indicator hA
  have hFzero : MeasurableSet {path : ℝ≥0 → ℝ | F path = 0} :=
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage hFm
  have hVm : Measurable V :=
    Measurable.ite hFzero measurable_const measurable_const
  have hFactor :=
    avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
      X s H hHm V hVm
  have hVoid : ∀ ω : Ω,
      V (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) =
        (if ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ B) = 0 then (1 : ℝ≥0∞) else 0) := by
    intro ω
    simp only [V, ← hFrep ω]
  simpa only [H, hVoid] using hFactor
