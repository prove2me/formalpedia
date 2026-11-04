-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:06.843196+00:00
-- url     : https://prove2.me/submissions/bf9bf576-c26a-43cf-a235-e9d1d2758702

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A continuous original-source small-jump map with the L2 variance isometry on a dense class of simple inputs preserves the norm everywhere. The source simple isometry is explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (S : Set (Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))))
        (hDense : Dense S)
        (hSimpleIso : ∀ v ∈ S, ‖I v‖ = ‖v‖),
      ∀ v, ‖I v‖ = ‖v‖) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro I S hDense hSimpleIso
  have hEq : Set.EqOn (fun v => ‖I v‖) (fun v => ‖v‖) S := by
    intro v hv
    exact hSimpleIso v hv
  have hAll : (fun v => ‖I v‖) = (fun v => ‖v‖) :=
    Continuous.ext_on hDense I.continuous.norm continuous_norm hEq
  intro v
  exact congrArg (fun f => f v) hAll
