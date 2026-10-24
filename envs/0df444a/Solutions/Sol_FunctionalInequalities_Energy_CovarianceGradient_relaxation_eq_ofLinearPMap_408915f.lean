-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:51:20.359549+00:00
-- url     : https://prove2.me/submissions/01e90b6b-2954-4ba3-9d29-c7f192af0512

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
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
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_weightedTest_iff_exists_test_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end
end
end

section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Functional
end FunctionalInequalities.Energy.Functional
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Functional
variable {X : Type*}
/-- Extended energy functionals are equal when all of their values are equal. -/
@[ext]
theorem FunctionalInequalities.Energy.Functional.ext {left right : Functional X} (h : ∀ x, left x = right x) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr
      funext x
      exact h x
end
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
section Operator
variable [MeasurableSpace V] (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : Measure V} [m.IsAddHaarMeasure]
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
open WeightedGradient
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance density is the squared weighted gradient. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    density ν g = fun x ↦ ‖apply B g x‖ ^ 2 := by
  funext x
  exact hB _
end
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
section
namespace FunctionalInequalities.Energy.CovarianceGradient.Test
end FunctionalInequalities.Energy.CovarianceGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient FunctionalInequalities.Energy.CovarianceGradient.Test
open WeightedGradient
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance energy of a test is the squared `L²` norm of its
weighted gradient. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.Test.coe_energy_eq_norm_sq
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2)
    (f : Energy.CovarianceGradient.Test ν) (h : IsTest ν B f.toFun) :
    (f.energy : ℝ) = ‖h.memLp_apply.toLp (apply B f.toFun)‖ ^ 2 := by
  rw [coe_energy, L2.norm_toLp_sq,
    Energy.CovarianceGradient.density_eq_norm_sq ν B hB]
end
end
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
open WeightedGradient
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities.Energy.CovarianceGradient in
/-- The covariance relaxation is the sequential relaxation of the squared-norm pre-energy of the
weighted gradient operator, whenever `⟪Σ v, v⟫ = ‖B v‖²`. -/
theorem solution (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hB : ∀ v, inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) :
    FunctionalInequalities.Energy.CovarianceGradient.relaxation ν =
      (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac)).sequentialRelaxation := by
  ext x
  apply le_antisymm
  · refine (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac)).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.CovarianceGradient.preEnergy ν) id continuous_id ?_ x
    intro t
    let t' : (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac).domain := t
    obtain ⟨g, h, hg⟩ := (FunctionalInequalities.Energy.WeightedGradient.mem_domain_operator_iff ν B hac t').mp t'.2
    obtain ⟨f, rfl⟩ := (FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test_408915f ν B hB g).mp h
    refine ⟨f, ?_, le_of_eq ?_⟩
    · change f.toL2 = (t' : Lp ℝ 2 (ν : Measure V))
      rw [hg]
      rfl
    · apply NNReal.eq
      change (f.energy : ℝ) =
        ((‖FunctionalInequalities.Energy.WeightedGradient.operator ν B hac ⟨(t' : Lp ℝ 2 (ν : Measure V)), t'.2⟩‖₊ ^ 2 : NNReal) : ℝ)
      rw [FunctionalInequalities.Energy.CovarianceGradient.Test.coe_energy_eq_norm_sq ν B hB f h, FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac hfr h t'.2 hg]
      push_cast
      rfl
  · refine (FunctionalInequalities.Energy.CovarianceGradient.preEnergy ν).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac)) id continuous_id ?_ x
    intro f
    have h : FunctionalInequalities.Energy.WeightedGradient.IsTest ν B f.toFun :=
      (FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test_408915f ν B hB f.toFun).mpr ⟨f, rfl⟩
    have hmem : f.toL2 ∈ (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac).domain :=
      FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν B hac h
    refine ⟨⟨f.toL2, hmem⟩, rfl, le_of_eq ?_⟩
    apply NNReal.eq
    change ((‖FunctionalInequalities.Energy.WeightedGradient.operator ν B hac ⟨f.toL2, hmem⟩‖₊ ^ 2 : NNReal) : ℝ) = (f.energy : ℝ)
    rw [FunctionalInequalities.Energy.CovarianceGradient.Test.coe_energy_eq_norm_sq ν B hB f h, FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac hfr h hmem rfl]
    push_cast
    rfl
