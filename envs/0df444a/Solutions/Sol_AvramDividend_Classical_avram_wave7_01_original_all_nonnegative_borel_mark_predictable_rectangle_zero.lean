-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_all_nonnegative_borel_mark_predictable_rectangle_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:28:52.09967+00:00
-- url     : https://prove2.me/submissions/1a0fa132-8fff-4a5c-bbb7-a88ec417d956

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! Original source predictable compensation on every nonnegative mark set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNonneg : B ⊆ Ici (0 : ℝ)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hν : X.ν B = 0 := by
    apply le_antisymm
    · calc
        X.ν B ≤ X.ν (Ici (0 : ℝ)) := measure_mono hNonneg
        _ = 0 := X.ν_Ici
    · exact bot_le
  have hsubRect : Ioc s t ×ˢ B ⊆
      (Set.univ : Set ℝ≥0) ×ˢ Ici (0 : ℝ) := by
    intro z hz
    exact ⟨Set.mem_univ _, hNonneg hz.2⟩
  have hCount (ω : Ω) :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0 := by
    let μ : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    change μ (Ioc s t ×ˢ B) = 0
    apply le_antisymm
    · calc
        μ (Ioc s t ×ˢ B) ≤ μ ((Set.univ : Set ℝ≥0) ×ˢ Ici (0 : ℝ)) :=
          measure_mono hsubRect
        _ = 0 := avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero X ω
    · exact bot_le
  simp only [hCount, lintegral_zero, hν, mul_zero]
