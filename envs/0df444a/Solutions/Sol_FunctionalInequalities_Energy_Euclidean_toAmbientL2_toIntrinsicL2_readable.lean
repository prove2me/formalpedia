-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:54.139277+00:00
-- url     : https://prove2.me/submissions/d609bf58-d43d-4428-8211-a39edd3e2a8a

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic

noncomputable section
open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Returning to ambient coordinates after passing to intrinsic coordinates is the identity. -/
@[simp]
theorem solution (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    FunctionalInequalities.Energy.Euclidean.toAmbientL2 μ (FunctionalInequalities.Energy.Euclidean.toIntrinsicL2 μ f) = f := by
  change
    Lp.compMeasurePreserving (FunctionalInequalities.Probability.intrinsicMap μ)
        (FunctionalInequalities.Probability.measurePreserving_intrinsicMap μ)
        (Lp.compMeasurePreserving (FunctionalInequalities.Probability.reconstruct μ)
          (FunctionalInequalities.Probability.measurePreserving_reconstruct μ) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (FunctionalInequalities.Probability.measurePreserving_reconstruct μ)
    (FunctionalInequalities.Probability.measurePreserving_intrinsicMap μ)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving
        (FunctionalInequalities.Probability.reconstruct μ ∘ FunctionalInequalities.Probability.intrinsicMap μ)
        ((FunctionalInequalities.Probability.measurePreserving_reconstruct μ).comp
          (FunctionalInequalities.Probability.measurePreserving_intrinsicMap μ)) = f.1
  have hae :
      FunctionalInequalities.Probability.reconstruct μ ∘ FunctionalInequalities.Probability.intrinsicMap μ =ᵐ[(μ : Measure E)] id := by
    filter_upwards [FunctionalInequalities.Probability.reconstruct_intrinsicMap_ae μ] with x hx
    exact hx
  rw [AEEqFun.compMeasurePreserving_congr f.1
    ((FunctionalInequalities.Probability.measurePreserving_reconstruct μ).comp
      (FunctionalInequalities.Probability.measurePreserving_intrinsicMap μ))
    measurable_id hae]
  · exact AEEqFun.compMeasurePreserving_id f.1
