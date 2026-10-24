-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.exists_isDiffusion_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:07:58.148257+00:00
-- url     : https://prove2.me/submissions/3f73a6a0-5ad9-4c5c-b1c8-2e17bad41320

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Filtration
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Martingale
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Upcrossing
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Predictable
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_SimpleProcess
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Existence
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Setup
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariationSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFormulaGrid
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoLocality
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoOptionalStopping
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoPullOut
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoTruncate
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoVersionExists
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimIto
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_PolarisedQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SmoothCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardBieleckiNorm
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardContractionEstimate
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardContractionFixedPoint
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardGlobal
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputModification
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputStepDiff
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputWeighting
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceDiscrete
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStepMap
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStochasticLipschitz
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardWindow
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_Setting
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_CadlagModification
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Compensated
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDiff
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepWeight
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_StoppedProgressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionCoeffs_lipschitz_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_of_unbounded_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_vectorItoProcess_ae_eq_zero_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_exists_globalSolution_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_itoIntegral_congr_ae_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/Compensated.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Poisson
end LevyStochCalc.Poisson
open LevyStochCalc LevyStochCalc.Poisson
section
namespace LevyStochCalc.Poisson.Compensated
end LevyStochCalc.Poisson.Compensated
open LevyStochCalc LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
section Integral
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ
    : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
include hℱ in
/-- The Itô–Lévy isometry of the stochastic integral at every time `T > 0`. -/
theorem LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hT.le]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T]
    with ω hω
  rw [hω]
end Integral
end
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Ito
end LevyStochCalc.Ito
open LevyStochCalc LevyStochCalc.Ito
section
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc LevyStochCalc.Ito LevyStochCalc.Ito.Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
/-- The compensated-Poisson integral is measurable at each time. -/
theorem LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ hm hp hs t ω :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN φ hm hp hs
    t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl
end
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Ito
end LevyStochCalc.Ito
open LevyStochCalc LevyStochCalc.Ito
section
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc LevyStochCalc.Ito LevyStochCalc.Ito.Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
section Glue
variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
/-- A solution on a window starts at the initial datum. -/
theorem LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn (x₀ : Fin n → ℝ) {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hT : 0 ≤ T) (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ := by
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩,
    ae_picardStep_zero W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
      h.h_γ_meas h.h_γ_progMeas h.h_γ_sq] with ω h1 h2
  funext i
  rw [h1 i, h2 i]
end Glue
end
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
/-- A continuous function of a version is progressively measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.progressivelyMeasurable_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  refine MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => hφ.comp_stronglyMeasurable (h.adapted t)) fun ω => ?_
  exact hφ.comp (h.continuous_path ω)
/-- A measurable function of a version is jointly measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) : Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry
end VectorVersion
end
end
end
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
universe u
private theorem FunctionalInequalities.Probability.Diffusion.zeroPoisson_filtration {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Poisson.IsPoissonFiltration (FunctionalInequalities.Probability.Diffusion.zeroPoisson P) ℱ := by
  constructor
  · intro t B _ _
    exact measurable_const
  · intro s _
    change Indep (ℱ s)
      (⨆ D ∈ {D : Set (ℝ × Unit) |
          D ⊆ Set.Ioi s ×ˢ Set.univ ∧ MeasurableSet D},
        MeasurableSpace.comap (fun _ : Ω => (0 : ℝ≥0∞)) inferInstance) P
    simp only [MeasurableSpace.comap_const, iSup_bot]
    exact indep_bot_right _
private theorem FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_regular {N d : ℕ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ}
    (hb : Measurable b) (hσ : ∀ k, Measurable fun x => σ x k) :
    (FunctionalInequalities.Probability.Diffusion.diffusionCoeffs b σ).IsRegular (0 : Measure Unit) := by
  refine ⟨hb.comp measurable_snd, ?_, measurable_const, ?_, ?_, ?_⟩
  · exact measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun k => ((hσ k).eval (a := i)).comp measurable_snd
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T, (‖b 0‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      isCompact_Icc.measure_lt_top
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T,
      ∑ i, ∑ k, (‖σ 0 k i‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤
    rw [lintegral_const, Measure.restrict_apply_univ]
    refine ENNReal.mul_lt_top ?_ isCompact_Icc.measure_lt_top
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.pow_lt_top ENNReal.coe_lt_top
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T,
      ∫⁻ _e, (‖(0 : Fin N → ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂(0 : Measure Unit) ∂volume) < ⊤
    simp
section Diffusion
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {N d : ℕ}
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.Probability.Diffusion in
open LevyStochCalc.Ito.Picard in
/-- Globally Lipschitz bounded autonomous coefficients with zero jumps: an everywhere continuous adapted
solution with Itô representation along itself exists on any Brownian setup with a usual filtration. -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k)
    {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B) (hσB : ∀ x k, ‖σ x k‖ ≤ B) (x₀ : Fin N → ℝ) :
    ∃ Y : ℝ → Ω → Fin N → ℝ, FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW b σ x₀ Y := by
  classical
  let C := FunctionalInequalities.Probability.Diffusion.diffusionCoeffs b σ
  let Z := FunctionalInequalities.Probability.Diffusion.zeroPoisson P
  have hZ : LevyStochCalc.Poisson.IsPoissonFiltration Z ℱ := zeroPoisson_filtration P ℱ
  have hReg : C.IsRegular (0 : Measure Unit) :=
    diffusionCoeffs_regular hb.continuous.measurable
      (fun k => (hσ k).continuous.measurable)
  obtain ⟨L, hLip⟩ := FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_lipschitz_408915f hb hσ
  obtain ⟨X, hXm, hXp, _hX0, _hXcad, _hXS, hSol⟩ :=
    LevyStochCalc.Ito.Picard.exists_globalSolution_408915f W Z ℱ hW hZ C hℱ0 hnull hReg hLip x₀
  let S := hSol 0
  let H : Fin N → Fin d → Ω → ℝ → ℝ := fun i k ω s => σ (X s ω) k i
  let a : Fin N → Ω → ℝ → ℝ := fun i ω s => b (X s ω) i
  have hm : ∀ i k, Measurable (Function.uncurry (H i k)) := S.h_σ_meas
  have hp : ∀ i k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H i k) := S.h_σ_progMeas
  have hq : ∀ i k (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H i k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := S.h_σ_sq
  have ham : ∀ i, Measurable (Function.uncurry (a i)) :=
    LevyStochCalc.Ito.Picard.measurable_mu_comp_state C hReg hXm
  have hap : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (a i) := by
    intro i
    exact LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state (X := X)
      (f := fun _ x => b x i) hXp
      ((hb.continuous.measurable.eval (a := i)).comp measurable_snd)
  have haq : ∀ i (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro i
    exact LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded
      (fun ω s => (norm_le_pi_norm (b (X s ω)) i).trans (hbB (X s ω)))
  obtain ⟨Y, hY⟩ := LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded_408915f W ℱ hW H hm hp hq
    hℱ0 hnull (X₀ := fun _ => x₀) (fun _ => measurable_const) a ham hap haq
  have hXrep : ∀ t : ℝ, 0 ≤ t →
      X t =ᵐ[P] LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hW H hm hp hq (fun _ => x₀) a t := by
    intro t ht
    rcases eq_or_lt_of_le ht with he | ht
    · rw [← he]
      filter_upwards
        [LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn W Z ℱ hW hZ C x₀ le_rfl (hSol 0),
          LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_408915f W ℱ hW hm hp hq (fun _ => x₀) a]
        with ω hXω hVω
      exact hXω.trans hVω.symm
    · have hj : ∀ᵐ ω ∂P, ∀ i : Fin N,
          LevyStochCalc.Ito.Picard.picardStep_jump Z ℱ hZ C X S.h_γ_meas S.h_γ_progMeas S.h_γ_sq t ω i = 0 := by
        apply ae_all_iff.mpr
        intro i
        have hiso := LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral Z ℱ hZ
          (fun ω s e => C.γ s (X s ω) e i)
          (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ht
        have hjm := LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice Z ℱ hZ
          (fun ω s e => C.γ s (X s ω) e i)
          (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t
        have hz : (∫⁻ ω,
            (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral Z ℱ hZ
              (fun ω s e => C.γ s (X s ω) e i)
              (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) = 0 := by
          simpa using hiso
        filter_upwards [(lintegral_eq_zero_iff
          ((hjm.nnnorm.coe_nnreal_ennreal).pow_const 2)).mp hz] with ω hω
        change LevyStochCalc.Poisson.Compensated.stochasticIntegral Z ℱ hZ
          (fun ω s e => C.γ s (X s ω) e i)
          (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ω = 0
        simpa using hω
      filter_upwards [(hSol t).eqn t ⟨ht.le, le_rfl⟩, hj] with ω heq hz
      funext i
      have hi := heq i
      change X t ω i =
        LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hW H hm hp hq (fun _ => x₀) a t ω i +
          LevyStochCalc.Ito.Picard.picardStep_jump Z ℱ hZ C X S.h_γ_meas S.h_γ_progMeas S.h_γ_sq t ω i at hi
      simpa only [hz i, add_zero] using hi
  have hXY : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] Y t :=
    fun t ht => (hXrep t ht).trans (hY.ae_eq t ht).symm
  have hXY_window : ∀ t : ℝ,
      ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) t), X s ω = Y s ω := by
    intro t
    have he : MeasurableSet {p : Ω × ℝ | X p.2 p.1 = Y p.2 p.1} :=
      measurableSet_eq_fun (hXm.comp measurable_swap) hY.measurable_uncurry
    apply (Measure.ae_ae_comm (p := fun ω s => X s ω = Y s ω) he).mpr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    exact hXY s hs.1
  let G : Fin N → Fin d → Ω → ℝ → ℝ := fun i k ω s => σ (Y s ω) k i
  let c : Fin N → Ω → ℝ → ℝ := fun i ω s => b (Y s ω) i
  have gm : ∀ i k, Measurable (Function.uncurry (G i k)) := by
    intro i k
    exact hY.measurable_uncurry_comp ((hσ k).continuous.measurable.eval (a := i))
  have gp : ∀ i k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (G i k) := by
    intro i k
    exact hY.progressivelyMeasurable_comp ((continuous_apply i).comp (hσ k).continuous)
  have gq : ∀ i k (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G i k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro i k
    exact LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded
      (fun ω s => (norm_le_pi_norm (σ (Y s ω) k) i).trans (hσB (Y s ω) k))
  refine ⟨Y, gm, gp, gq, hY.continuous_path, hY.adapted, ?_⟩
  intro t ht
  refine (hY.ae_eq t ht).trans ?_
  rcases eq_or_lt_of_le ht with he | ht
  · subst t
    exact (LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_408915f W ℱ hW hm hp hq (fun _ => x₀) a).trans
      (LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_408915f W ℱ hW gm gp gq (fun _ => x₀) c).symm
  · have hI : ∀ᵐ ω ∂P, ∀ (i : Fin N) (k : Fin d),
        LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hW H hm hp hq i k t ω =
          LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hW G gm gp gq i k t ω := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro k
      apply LevyStochCalc.Ito.Picard.itoIntegral_congr_ae_408915f (W.W k) ℱ (hW k)
        (H i k) (G i k) (hm i k) (hp i k) (hq i k)
        (gm i k) (gp i k) (gq i k) ht
      filter_upwards [hXY_window t] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (fun x => σ x k i) hs
    filter_upwards [hXY_window t, hI] with ω hω hIω
    funext i
    have ha : (∫ s in Set.Icc (0 : ℝ) t, a i ω s ∂volume) =
        ∫ s in Set.Icc (0 : ℝ) t, c i ω s ∂volume := by
      apply integral_congr_ae
      filter_upwards [hω] with s hs
      exact congrArg (fun x => b x i) hs
    have hM : LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW H hm hp hq i t ω =
        LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW G gm gp gq i t ω :=
      Finset.sum_congr rfl fun k _ => hIω i k
    change x₀ i + (∫ s in Set.Icc (0 : ℝ) t, a i ω s ∂volume) +
        LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW H hm hp hq i t ω =
      x₀ i + (∫ s in Set.Icc (0 : ℝ) t, c i ω s ∂volume) +
        LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW G gm gp gq i t ω
    rw [ha, hM]
