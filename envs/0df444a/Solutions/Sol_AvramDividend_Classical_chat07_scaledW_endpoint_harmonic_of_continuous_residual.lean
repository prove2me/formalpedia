-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scaledW_endpoint_harmonic_of_continuous_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:36:36.056717+00:00
-- url     : https://prove2.me/submissions/2faba150-8089-444e-80bc-71c9b98cf35c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_harmonic_at_endpoint_of_continuity
import Theorems.Thm_AvramDividend_Classical_scaledW_generator_harmonic_of_scale_harmonic_at_positive
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a : ℝ) (ha : 0 < a)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) a ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a -
        q * divE (W a) (scaleDeriv W a) = 0 := by
  obtain ⟨hdomW, hharmW⟩ :=
    generator_harmonic_at_endpoint_of_continuity
      X q W a ha hdom hcont hinside
  exact scaledW_generator_harmonic_of_scale_harmonic_at_positive
    X q W a ha hdomW hharmW
