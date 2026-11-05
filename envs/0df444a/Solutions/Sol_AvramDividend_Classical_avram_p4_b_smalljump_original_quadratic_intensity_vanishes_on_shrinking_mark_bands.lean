-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_intensity_vanishes_on_shrinking_mark_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:57:41.890722+00:00
-- url     : https://prove2.me/submissions/5961291a-3053-460a-a0f6-896049173950

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Continuity from above for the original source Lévy quadratic-jump
intensity on shrinking Borel neighbourhoods of the origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ))
    (hFinite :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))) Set.univ < ⊤)
    (hZero :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        ({0} : Set ℝ) = 0) :
    Tendsto (fun n =>
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        (B n)) atTop (𝓝 0) := by
  let ν₂ : Measure ℝ :=
    X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))
  have hf : ν₂ (B 0) ≠ ⊤ := by
    have hle : ν₂ (B 0) ≤ ν₂ Set.univ :=
      measure_mono (Set.subset_univ _)
    exact ne_of_lt (lt_of_le_of_lt hle hFinite)
  have hInterZero : ν₂ (⋂ n, B n) = 0 := by
    have hZeroNu : ν₂ ({0} : Set ℝ) = 0 := hZero
    apply le_antisymm
    · have hm : ν₂ (⋂ n, B n) ≤ ν₂ ({0} : Set ℝ) :=
        measure_mono hInter
      exact hm.trans_eq hZeroNu
    · exact zero_le
  have hCont := tendsto_measure_iInter_atTop
    (fun n => (hB n).nullMeasurableSet) hAnti ⟨0, hf⟩
    (μ := ν₂)
  simpa only [Function.comp_def, hInterZero] using hCont
