-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_nonnegative_borel_marks_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:38:17.372909+00:00
-- url     : https://prove2.me/submissions/2e54b98e-9606-4143-9107-58a69df155b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Nonnegative Borel marks have neither literal original jumps nor source
Lévy measure mass, including zero-sized jumps and empty time windows. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hBnonneg : B ⊆ Ici (0 : ℝ)) :
    (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0) ∧
    X.ν B = 0 ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hEmpty : B ∩ Iio (0 : ℝ) = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hyB, hyneg⟩
    exact (not_lt_of_ge (hBnonneg hyB)) hyneg
  have hN : ∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0 := by
    intro ω
    calc
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) :=
        avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
          X ω s t B hB
      _ = 0 := by simp [hEmpty]
  have hν : X.ν B = 0 := by
    rw [avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction X B hB]
    simp [hEmpty]
  refine ⟨hN, hν, ?_⟩
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) :=
      lintegral_congr hN
    _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by simp [hν]
