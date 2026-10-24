-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:42:05.731924+00:00
-- url     : https://prove2.me/submissions/6c11d542-d2bc-4fa3-86dc-60ebaaabb58b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_LipschitzGradient_holds_ofPreEnergy_of_localSlope_408915f
import Theorems.Thm_FunctionalInequalities_Energy_LipschitzGradient_localSlope_holds_of_relaxation_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_TestFamily_holds_ofPreEnergy_iff_408915f

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
universe u
section
namespace FunctionalInequalities.Poincare.TestFamily
end FunctionalInequalities.Poincare.TestFamily
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.TestFamily
/-- The extended Rayleigh quotient is bounded by a finite `C` exactly when the defining
inequality holds. This includes zero-energy tests, whose quotient may be infinite. -/
theorem FunctionalInequalities.Poincare.TestFamily.rayleigh_le_iff (F : TestFamily) (f : F.Test) (C : NNReal) :
    rayleigh F f ≤ (C : ENNReal) ↔ F.variance f ≤ C * F.energy f := by
  rw [rayleigh, ENNReal.div_le_iff_le_mul
    (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
/-- A finite constant is valid exactly when it bounds the optimal extended constant. -/
theorem FunctionalInequalities.Poincare.TestFamily.holds_iff_constant_le (F : TestFamily) (C : NNReal) :
    Holds F C ↔ constant F ≤ (C : ENNReal) := by
  rw [constant, iSup_le_iff]
  exact forall_congr' fun f ↦ (rayleigh_le_iff F f C).symm
end
end
end
end
end

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
universe u
variable {α : Type u} [MeasurableSpace α]
section
namespace FunctionalInequalities.Poincare.L2Energy
end FunctionalInequalities.Poincare.L2Energy
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.L2Energy
/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔ constant μ energy ≤ (C : ENNReal) := by
  simpa [Holds, constant] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local order consequence of `constant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl
/-- Source: local order consequence of `constant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem FunctionalInequalities.Poincare.SmoothTest.le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
section Bridge
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.LipschitzGradient
end FunctionalInequalities.Poincare.LipschitzGradient
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.LipschitzGradient
/-- A finite constant is valid for the Lipschitz gradient relaxation exactly when it is a literature
constant. -/
theorem FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (C : NNReal) :
    Poincare.L2Energy.Holds ν (Energy.LipschitzGradient.relaxation ν m hac) C ↔ Poincare.LocalSlope.Holds ν C :=
  ⟨Energy.LipschitzGradient.localSlope_holds_of_relaxation_408915f ν m hac hfr, fun h ↦
    (Poincare.TestFamily.holds_ofPreEnergy_iff_408915f ν _ C).mp
      (Energy.LipschitzGradient.holds_ofPreEnergy_of_localSlope_408915f ν m hac hfr h)⟩
end
end
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities.Poincare.SmoothTest in
/-- The smooth-test constant equals the optimal constant of the Lipschitz gradient
relaxation. -/
theorem solution
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    FunctionalInequalities.Poincare.SmoothTest.constant (ν : Measure V) =
      FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) := by
  apply le_antisymm
  · by_cases htop : FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) = ⊤
    · rw [htop]
      exact le_top
    · set C := (FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac)).toNNReal
      have hC : FunctionalInequalities.Poincare.L2Energy.Holds ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) C :=
        (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have hlit := (FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope
        ν m hac hfr C).mp hC
      have hlegacy := (FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_408915f ν m hac C).mpr hlit
      rw [← ENNReal.coe_toNNReal htop]
      exact FunctionalInequalities.Poincare.SmoothTest.constant_le hlegacy
  · apply FunctionalInequalities.Poincare.SmoothTest.le_constant
    intro C hC
    have hlit := (FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_408915f ν m hac C).mp hC
    exact (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mp
      ((FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope ν m hac hfr C).mpr hlit)
