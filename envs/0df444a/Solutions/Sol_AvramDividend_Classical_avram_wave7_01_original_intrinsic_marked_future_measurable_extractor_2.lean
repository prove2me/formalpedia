-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:47:03.568883+00:00
-- url     : https://prove2.me/submissions/deb906b5-b299-43ce-9cf6-3b261fdacdec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original future extractor follows from genuine universal càdlàg
marked-jump extraction and the proved same-path original clock transport. -/
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
  obtain ⟨F, hF, hCount⟩ :=
    avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
      (t - s) B hB
  refine ⟨F, hF, ?_⟩
  intro ω
  have hReg :=
    avram_wave7_01_original_shifted_future_increment_path_cadlag X ω s
  calc
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
      = ({v : ℝ≥0 | 0 < v ∧ v ≤ t - s ∧
          (X.X (s + v) ω - X.X s ω) -
            Function.leftLim
              (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ≠ 0 ∧
          (X.X (s + v) ω - X.X s ω) -
            Function.leftLim
              (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ∈ B}).encard := by
          simpa only [add_tsub_cancel_of_le hst] using
            (avram_wave5_01_actual_source_futurepath_marked_count_transport
              X ω s (t - s) B hB)
    _ = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) :=
      hCount _ hReg.1 hReg.2
