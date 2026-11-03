-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_consecutive_predictable_weighted_cells_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:27:56.894429+00:00
-- url     : https://prove2.me/submissions/78d50626-5ecc-4392-b349-f663f2d71675

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- An earlier predictably weighted original centred cell is orthogonal to the
next centred source increment even after multiplication by the next predictable
weight. The combined earlier weight is assumed integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s] W₀)
    (hW₁ : Measurable[𝓕 (s + u)] W₁)
    (hXI : Integrable (X.X v) P)
    (hProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) * W₁ ω) P) :
    (∫ ω, ((W₀ ω * (X.X (s + u) ω - X.X s ω -
      (∫ η, X.X u η ∂P))) * W₁ ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)) ∂P) = 0 := by
  let W : Ω → ℝ := fun ω =>
    (W₀ ω * (X.X (s + u) ω - X.X s ω -
      (∫ η, X.X u η ∂P))) * W₁ ω
  have hle : s ≤ s + u := by simp
  have hW₀Next : Measurable[𝓕 (s + u)] W₀ :=
    hW₀.mono (𝓕.mono hle) le_rfl
  have hEnd : Measurable[𝓕 (s + u)] (X.X (s + u)) :=
    X.adapted.measurable_le le_rfl
  have hStart : Measurable[𝓕 (s + u)] (X.X s) :=
    X.adapted.measurable_le hle
  have hWNext : Measurable[𝓕 (s + u)] W := by
    letI : MeasurableSpace Ω := 𝓕 (s + u)
    exact (hW₀Next.mul ((hEnd.sub hStart).sub measurable_const)).mul hW₁
  have hWI : Integrable W P := hProduct
  have hZero :=
    avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
      X (s + u) v W hWNext hWI hXI
  simpa only [W] using hZero
