-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:14.377691+00:00
-- url     : https://prove2.me/submissions/3e65f317-6f02-40a4-bf8e-bdeaaceeacc3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A continuous original-source compensated map has zero value under a bounded expectation functional on all integrands whenever zero centring holds on a dense simple class. The source simple centring is explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (J : Lp ℝ (2 : ℝ≥0∞) P →L[ℝ] ℝ)
        (S : Set (Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))))
        (hDense : Dense S)
        (hSimpleZero : ∀ v ∈ S, J (I v) = 0),
      ∀ v, J (I v) = 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro I J S hDense hSimpleZero
  have hEq : Set.EqOn (fun v => J (I v)) (fun _ => (0 : ℝ)) S := by
    intro v hv
    exact hSimpleZero v hv
  have hAll : (fun v => J (I v)) = (fun _ => (0 : ℝ)) :=
    Continuous.ext_on hDense (J.continuous.comp I.continuous) continuous_const hEq
  intro v
  exact congrArg (fun f => f v) hAll
