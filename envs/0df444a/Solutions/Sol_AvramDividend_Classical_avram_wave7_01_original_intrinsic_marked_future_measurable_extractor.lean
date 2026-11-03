-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:47:33.105953+00:00
-- url     : https://prove2.me/submissions/8a559435-c1c8-4e7a-ac0b-ac89bcc4cf84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_interval_samepath_marked_count
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! Exact source measurable future-extractor target reduced to genuine generic
cadlag Borel jump measurability, with the actual shifted source path regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) := by
  obtain ⟨F, hF, hEval⟩ :=
    avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
      (t - s) B hB
  refine ⟨F, hF, ?_⟩
  intro ω
  have hCad :=
    avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
  calc
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
      ({v : ℝ≥0 | 0 < v ∧ v ≤ t - s ∧
        (X.X (s + v) ω - X.X s ω) -
          Function.leftLim
            (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ≠ 0 ∧
        (X.X (s + v) ω - X.X s ω) -
          Function.leftLim
            (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ∈ B}).encard :=
      avram_wave7_01_original_arbitrary_interval_samepath_marked_count
        X ω s t hst B hB
    _ = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) :=
      hEval _ hCad.1 hCad.2
