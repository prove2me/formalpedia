-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:51:02.590072+00:00
-- url     : https://prove2.me/submissions/d008a184-3d25-495c-b24c-e5970f05e709

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
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
import Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_408915f

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
omit [SecondCountableTopology V₁] in
/-- The covariance operator of the image law. -/
theorem FunctionalInequalities.Covariance.operator_mapContinuousLinearEquiv :
    Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp
        (T : V₁ →L[ℝ] V₂).adjoint :=
  Covariance.operator_map_continuousLinearEquiv_408915f (ν : Measure V₁) T
omit [SecondCountableTopology V₁] in
/-- The covariance quadratic form of the image law, read through the adjoint. -/
theorem FunctionalInequalities.Covariance.inner_operator_mapContinuousLinearEquiv (w : V₂) :
    inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w) := by
  rw [Covariance.operator_mapContinuousLinearEquiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂) _ w).symm
omit [SecondCountableTopology V₁] in
/-- The covariance quadratic form of `ν`, read through the adjoint of the inverse. -/
theorem FunctionalInequalities.Covariance.inner_operator_mapContinuousLinearEquiv_symm (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂)
        ((T.symm : V₂ →L[ℝ] V₁).adjoint w)) ((T.symm : V₂ →L[ℝ] V₁).adjoint w) := by
  rw [Covariance.inner_operator_mapContinuousLinearEquiv]
  have hT : (T : V₁ →L[ℝ] V₂).adjoint ((T.symm : V₂ →L[ℝ] V₁).adjoint w) = w := by
    have hcomp : (T.symm : V₂ →L[ℝ] V₁).comp (T : V₁ →L[ℝ] V₂) = ContinuousLinearMap.id ℝ V₁ := by
      ext x
      simp
    have := congrArg (fun A : V₁ →L[ℝ] V₁ ↦ A.adjoint w) hcomp
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using this
  rw [hT]
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
end ContinuousLinearEquiv
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
universe u v
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
section Tests
variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
variable {ν₁ : ProbabilityMeasure V₁} {ν₂ : ProbabilityMeasure V₂} {T : V₁ ≃L[ℝ] V₂}
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
section
namespace FunctionalInequalities.Energy.CovarianceGradient.Test
end FunctionalInequalities.Energy.CovarianceGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient FunctionalInequalities.Energy.CovarianceGradient.Test
omit [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The composed test has the same covariance energy. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.Test.energy_compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : Test ν₂) :
    (g.compContinuousLinearEquiv hmp hcov).energy = g.energy := by
  apply NNReal.eq
  simp only [coe_energy]
  have hdens : density ν₁ (g.compContinuousLinearEquiv hmp hcov).toFun =
      density ν₂ g.toFun ∘ T := by
    funext x
    simp only [compContinuousLinearEquiv, density,
      Function.comp_apply, gradient_comp_continuousLinearEquiv, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl
omit [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The composed test realizes the pullback of the original class. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.Test.toL2_compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : Test ν₂) :
    (g.compContinuousLinearEquiv hmp hcov).toL2 = Lp.compMeasurePreserving T hmp g.toL2 := by
  apply Lp.ext
  refine (g.compContinuousLinearEquiv hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm
end
end
end Tests
section Relaxation
variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities.Energy.CovarianceGradient in
omit [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂] in
omit [SecondCountableTopology V₁] in
/-- The covariance relaxation of the image law is the covariance relaxation of `ν` pulled back
along `T`. -/
theorem solution (f : Lp ℝ 2 (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    FunctionalInequalities.Energy.CovarianceGradient.relaxation (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T) f = FunctionalInequalities.Energy.CovarianceGradient.relaxation ν (FunctionalInequalities.L2.ContinuousLinearEquiv.pullbackEquiv ν T f) := by
  have hcov : ∀ w, inner ℝ (FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T : Measure V₂) w) w =
      inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w) :=
    FunctionalInequalities.Covariance.inner_operator_mapContinuousLinearEquiv ν T
  have hcov' : ∀ w, inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T : Measure V₂)
        ((T.symm : V₂ →L[ℝ] V₁).adjoint w)) ((T.symm : V₂ →L[ℝ] V₁).adjoint w) :=
    FunctionalInequalities.Covariance.inner_operator_mapContinuousLinearEquiv_symm ν T
  apply le_antisymm
  · have h := (FunctionalInequalities.Energy.CovarianceGradient.preEnergy ν).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T)) (FunctionalInequalities.L2.ContinuousLinearEquiv.pullbackInv ν T)
      (FunctionalInequalities.L2.ContinuousLinearEquiv.pullbackInv ν T).continuous ?_ (FunctionalInequalities.L2.ContinuousLinearEquiv.pullbackEquiv ν T f)
    · rw [FunctionalInequalities.L2.ContinuousLinearEquiv.pullbackEquiv_apply, FunctionalInequalities.L2.ContinuousLinearEquiv.pullbackInv_pullback] at h
      exact h
    · intro g
      refine ⟨g.compContinuousLinearEquiv (FunctionalInequalities.Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T) hcov', ?_,
        le_of_eq ?_⟩
      · exact g.toL2_compContinuousLinearEquiv _ _
      · exact g.energy_compContinuousLinearEquiv _ _
  · have h := (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (FunctionalInequalities.Probability.mapContinuousLinearEquiv ν T)).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.CovarianceGradient.preEnergy ν) (FunctionalInequalities.L2.ContinuousLinearEquiv.pullback ν T) (FunctionalInequalities.L2.ContinuousLinearEquiv.pullback ν T).continuous ?_ f
    · exact h
    · intro g
      refine ⟨g.compContinuousLinearEquiv (FunctionalInequalities.Probability.measurePreserving_mapContinuousLinearEquiv ν T) hcov, ?_,
        le_of_eq ?_⟩
      · exact g.toL2_compContinuousLinearEquiv _ _
      · exact g.energy_compContinuousLinearEquiv _ _
