-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.relaxation_translateLaw_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:51:04.147783+00:00
-- url     : https://prove2.me/submissions/082ec013-e6fa-4580-a000-7eca6ea8a578

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
variable [CompleteSpace V]
/-- Translation does not change the covariance operator. -/
theorem FunctionalInequalities.Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]
end Translation
end
end
end

section
noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u v
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
/-- A continuous map with energy-nonincreasing lifts on concrete tests has the same bound
after relaxation. Neither test class needs to be nonempty or densely realized.

Each source test must have one target test realizing its image exactly. For comparison by
approximating sequences in a common pseudometric space, see
`PreEnergy.sequentialRelaxation_le_of_recovery_sequences` in
`FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous`. The present result only needs
topological ambient spaces and also allows a map between different spaces.
-/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ Q.energy g ≤ P.energy f) (x : X) :
    Q.sequentialRelaxation (T x) ≤ P.sequentialRelaxation x := by
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun s ↦ ?_
  choose g hreal henergy using fun n ↦ h (s.1 n)
  have hconv : Tendsto (fun n ↦ Q.toAmbient (g n)) atTop (𝓝 (T x)) := by
    simpa only [hreal, Function.comp_def] using (hT.tendsto x).comp s.2
  exact (Q.sequentialRelaxation_le_sequenceEnergy ⟨g, hconv⟩).trans
    (liminf_le_liminf (Eventually.of_forall fun n ↦ ENNReal.coe_le_coe.mpr (henergy n)))
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
section
namespace FunctionalInequalities.Energy.CovarianceGradient.Test
end FunctionalInequalities.Energy.CovarianceGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient FunctionalInequalities.Energy.CovarianceGradient.Test
variable {ν : ProbabilityMeasure V}
/-- The `L²` realization agrees almost everywhere with the original test function. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.Test.toL2_coeFn (f : Test ν) :
    f.toL2 =ᵐ[(ν : Measure V)] f.toFun :=
  f.memLp_two.coeFn_toLp
end
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Tests
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν₁ ν₂ : ProbabilityMeasure V} {c : V}
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
section
namespace FunctionalInequalities.Energy.CovarianceGradient.Test
end FunctionalInequalities.Energy.CovarianceGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient FunctionalInequalities.Energy.CovarianceGradient.Test
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The translated test has the same covariance energy. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.Test.energy_translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : Test ν₂) :
    (g.translate hmp hcov).energy = g.energy := by
  apply NNReal.eq
  simp only [coe_energy]
  have hdens : density ν₁ (g.translate hmp hcov).toFun =
      density ν₂ g.toFun ∘ fun x ↦ c + x := by
    funext x
    simp only [translate, density, Function.comp_apply,
      gradient_comp_const_add, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The translated test realizes the pullback of the original class. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.Test.toL2_translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : Test ν₂) :
    (g.translate hmp hcov).toL2 = Lp.compMeasurePreserving (fun x ↦ c + x) hmp g.toL2 := by
  apply Lp.ext
  refine (g.translate hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm
end
end
end Tests
section Relaxation
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (c : V)
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities.Energy.CovarianceGradient in
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The covariance relaxation of the translated law is the covariance relaxation of `ν` pulled
back along the translation isometry. -/
theorem solution (f : Lp ℝ 2 (FunctionalInequalities.Probability.translateLaw ν c : Measure V)) :
    FunctionalInequalities.Energy.CovarianceGradient.relaxation (FunctionalInequalities.Probability.translateLaw ν c) f = FunctionalInequalities.Energy.CovarianceGradient.relaxation ν (FunctionalInequalities.L2.Translation.pullbackEquiv ν c f) := by
  have hcov : FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.translateLaw ν c : Measure V) =
      FunctionalInequalities.Covariance.operator (ν : Measure V) := FunctionalInequalities.Covariance.operator_translateLaw ν c
  apply le_antisymm
  · -- pull tests of `ν` back to the translated law along the inverse translation
    have h := (FunctionalInequalities.Energy.CovarianceGradient.preEnergy ν).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (FunctionalInequalities.Probability.translateLaw ν c)) (FunctionalInequalities.L2.Translation.pullbackInv ν c)
      (FunctionalInequalities.L2.Translation.pullbackInv ν c).continuous ?_ (FunctionalInequalities.L2.Translation.pullbackEquiv ν c f)
    · rw [FunctionalInequalities.L2.Translation.pullbackEquiv_apply, FunctionalInequalities.L2.Translation.pullbackInv_pullback] at h
      exact h
    · intro g
      refine ⟨g.translate (FunctionalInequalities.Probability.measurePreserving_translate_symm ν c) hcov.symm, ?_, le_of_eq ?_⟩
      · exact g.toL2_translate _ _
      · exact g.energy_translate _ _
  · have h := (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (FunctionalInequalities.Probability.translateLaw ν c)).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.CovarianceGradient.preEnergy ν) (FunctionalInequalities.L2.Translation.pullback ν c) (FunctionalInequalities.L2.Translation.pullback ν c).continuous ?_ f
    · exact h
    · intro g
      refine ⟨g.translate (FunctionalInequalities.Probability.measurePreserving_translate ν c) hcov, ?_, le_of_eq ?_⟩
      · exact g.toL2_translate _ _
      · exact g.energy_translate _ _
