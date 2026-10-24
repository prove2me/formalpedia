-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:00.937479+00:00
-- url     : https://prove2.me/submissions/47355896-bf90-48d9-abfb-873604512d29

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Energy.Euclidean in
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
