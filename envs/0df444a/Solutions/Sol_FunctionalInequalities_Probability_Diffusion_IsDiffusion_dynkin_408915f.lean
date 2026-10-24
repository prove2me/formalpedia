-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:51:26.330977+00:00
-- url     : https://prove2.me/submissions/03286255-6bdc-46cf-a7d7-2a98fcb981f8

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
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
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
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
import Mathlib.LinearAlgebra.Basis.Fin
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_itoFormula_localise_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_of_unbounded_coeff_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_408915f

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

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Expansion
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- A continuous linear map on `Fin n → ℝ` is the sum of its values on the standard basis,
weighted by the coordinates. -/
theorem LevyStochCalc.clm_apply_pi (L : (Fin n → ℝ) →L[ℝ] F) (v : Fin n → ℝ) :
    L v = ∑ p, v p • L (Pi.single p 1) := by
  have hsingle : ∀ p : Fin n, (Pi.single p (v p) : Fin n → ℝ) = v p • Pi.single p (1 : ℝ) := by
    intro p
    rw [← Pi.single_smul']
    simp
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [hsingle p, map_smul]
/-- The scalar form of `clm_apply_pi`. -/
theorem LevyStochCalc.clm_apply_pi_real (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ p, v p * L (Pi.single p 1) := by
  simpa [smul_eq_mul] using clm_apply_pi L v
end Expansion
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- The first-order term of a Taylor expansion in coordinates. -/
theorem LevyStochCalc.apply_eq_sum_coordDeriv (x v : Fin n → ℝ) :
    f' x v = ∑ p, v p * coordDeriv f' p x :=
  clm_apply_pi_real (f' x) v
/-- The second-order term of a Taylor expansion in coordinates. -/
theorem LevyStochCalc.apply₂_eq_sum_coordDeriv₂ (x v : Fin n → ℝ) :
    f'' x v v = ∑ p, ∑ q, v p * v q * coordDeriv₂ f'' p q x := by
  have houter : f'' x v = ∑ p, v p • f'' x (Pi.single p 1) := clm_apply_pi (f'' x) v
  rw [houter, _root_.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, clm_apply_pi_real (f'' x (Pi.single p 1)) v,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [coordDeriv₂]; ring
/-- Continuity of a partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv (hf'c : Continuous f') (p : Fin n) :
    Continuous (coordDeriv f' p) :=
  hf'c.clm_apply continuous_const
/-- Continuity of a second partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv₂ (hf''c : Continuous f'') (p q : Fin n) :
    Continuous (coordDeriv₂ f'' p q) :=
  (hf''c.clm_apply continuous_const).clm_apply continuous_const
end Coord
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
section Limits
variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
variable (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')
/-- **Itô's formula for a twice continuously differentiable function of a vector Itô process
with unbounded coefficients.** -/
theorem LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume :=
  h.itoFormula_localise_408915f hfC hf hf' hmg hpg hqg hT
    (fun _g _g' _g'' _K₁ _K₂ hgf hgf' hK₁ hK₂0 hK₂ hg'c hg''c hunif hmG hpG hqG =>
      itoFormula_of_unbounded_coeff_408915f W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hgf hgf'
        (le_trans (norm_nonneg _) (hK₁ 0)) hK₁ hK₂0 hK₂ hg'c hg''c hunif hmG hpG hqG hT)
end Limits
end Clamped
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
private theorem FunctionalInequalities.Probability.Diffusion.compact_sum {α ι : Type*} [TopologicalSpace α]
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (0 : α → ℝ)
      exact HasCompactSupport.zero
  | @insert i s hi ih =>
      have hh := (hf i).add ih
      have he :
          (f i + fun x => ∑ j ∈ s, f j x) =
            (fun x => f i x + ∑ j ∈ s, f j x) := rfl
      rw [he] at hh
      simp only [Finset.sum_insert hi]
      exact hh
private theorem FunctionalInequalities.Probability.Diffusion.compact_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {g : (Fin N → ℝ) → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (Y : ℝ → Ω → Fin N → ℝ) :
    ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g (Y s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  exact energy_lt_top_of_bounded fun ω s => by
    simpa only [Real.norm_eq_abs] using hC (Y s ω)
private theorem FunctionalInequalities.Probability.Diffusion.compact_integral_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {g : (Fin N → ℝ) → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    {Y : ℝ → Ω → Fin N → ℝ}
    (hm : Measurable (Function.uncurry fun ω s => Y s ω)) (T : ℝ) :
    Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, g (Y s ω)) P := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  have hi : Integrable (Function.uncurry fun ω s => g (Y s ω))
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) :=
    Integrable.of_bound (hc.measurable.comp hm).aestronglyMeasurable C
      (Eventually.of_forall fun z => hC (Y z.2 z.1))
  exact hi.integral_prod_left
private theorem FunctionalInequalities.Probability.Diffusion.brownian_integrable_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (stochasticIntegralBrownian W ℱ hW H hm hp hq T) P ∧
      ∫ ω, stochasticIntegralBrownian W ℱ hW H hm hp hq T ω ∂P = 0 := by
  have hM := martingale_stochasticIntegralBrownian W ℱ hW H hm hp hq
  refine ⟨hM.integrable T, ?_⟩
  calc
    ∫ ω, stochasticIntegralBrownian W ℱ hW H hm hp hq T ω ∂P =
        ∫ ω, P[stochasticIntegralBrownian W ℱ hW H hm hp hq T | ℱ (-1)] ω ∂P :=
      (integral_condExp (ℱ.le (-1))).symm
    _ = ∫ ω, stochasticIntegralBrownian W ℱ hW H hm hp hq (-1) ω ∂P :=
      integral_congr_ae (hM.condExp_ae_eq (by linarith : (-1 : ℝ) ≤ T))
    _ = 0 := by
      rw [integral_congr_ae
        (stochasticIntegralBrownian_ae_zero_of_neg W ℱ hW H hm hp hq
          (by norm_num : (-1 : ℝ) < 0))]
      exact integral_zero _ _
section Diffusion
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {N d : ℕ}
namespace FunctionalInequalities.Probability.Diffusion.IsDiffusion
end FunctionalInequalities.Probability.Diffusion.IsDiffusion
open FunctionalInequalities.Probability.Diffusion.IsDiffusion in
set_option maxHeartbeats 1600000 in
/-- **Dynkin's identity**: for continuous compactly supported coefficients and `C²` `F`, `F(Y_T)` is
integrable and `E F(Y_T) − F(x₀) = E ∫₀ᵀ 𝓛F(Y_s) ds`. -/
theorem solution {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
    (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
    (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
    {Y : ℝ → Ω → Fin N → ℝ} (h : FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW b σ x₀ Y)
    {F : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (Y T ω)) P ∧
      ∫ ω, F (Y T ω) ∂P - F x₀ =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by
  classical
  obtain ⟨hm, hp, hq, hv⟩ := h
  have h0 := LevyStochCalc.Brownian.Ito.version_ae_eq_zero_408915f W ℱ hW hv
  by_cases ht : T = 0
  · subst T
    have he : (fun ω => F (Y 0 ω)) =ᵐ[P] fun _ => F x₀ :=
      h0.fun_comp F
    refine ⟨(integrable_const (F x₀)).congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    simp
  have ht : 0 < T := lt_of_le_of_ne hT (Ne.symm ht)
  let f' := fderiv ℝ F
  let f'' := fderiv ℝ f'
  have hf' : ContDiff ℝ 1 f' := hF.fderiv_right (by norm_num)
  have hf'c : Continuous f' := hf'.continuous
  have hf''c : Continuous f'' := hf'.continuous_fderiv (by norm_num)
  have hbc' (p : Fin N) : Continuous fun x => b x p :=
    (continuous_apply p).comp hbc
  have hbs' (p : Fin N) : HasCompactSupport fun x => b x p := by
    have hh := hbs.comp_left (g := fun z : Fin N → ℝ => z p) (by rfl)
    have he : ((fun z : Fin N → ℝ => z p) ∘ b) = (fun x => b x p) := rfl
    rw [he] at hh
    exact hh
  have hσc' (p : Fin N) (k : Fin d) : Continuous fun x => σ x k p :=
    (continuous_apply p).comp (hσc k)
  have hσs' (p : Fin N) (k : Fin d) : HasCompactSupport fun x => σ x k p := by
    have hh := (hσs k).comp_left (g := fun z : Fin N → ℝ => z p) (by rfl)
    have he :
        ((fun z : Fin N → ℝ => z p) ∘ fun x => σ x k) =
          (fun x => σ x k p) := rfl
    rw [he] at hh
    exact hh
  let A : Fin N → (Fin N → ℝ) → ℝ :=
    fun p x => LevyStochCalc.coordDeriv f' p x * b x p
  let C : Fin N → Fin N → (Fin N → ℝ) → ℝ :=
    fun p q x => LevyStochCalc.coordDeriv₂ f'' p q x * ∑ k, σ x k p * σ x k q
  let G : Fin N → Fin d → (Fin N → ℝ) → ℝ :=
    fun p k x => LevyStochCalc.coordDeriv f' p x * σ x k p
  have hAc (p : Fin N) : Continuous (A p) :=
    (LevyStochCalc.continuous_coordDeriv hf'c p).mul (hbc' p)
  have hAs (p : Fin N) : HasCompactSupport (A p) :=
    (hbs' p).mul_left
  have hCc (p q : Fin N) : Continuous (C p q) :=
    (LevyStochCalc.continuous_coordDeriv₂ hf''c p q).mul
      (continuous_finsetSum _ fun k _ => (hσc' p k).mul (hσc' q k))
  have hCs (p q : Fin N) : HasCompactSupport (C p q) :=
    (compact_sum Finset.univ (fun k x => σ x k p * σ x k q)
      (fun k => (hσs' p k).mul_right)).mul_left
  have hGc (p : Fin N) (k : Fin d) : Continuous (G p k) :=
    (LevyStochCalc.continuous_coordDeriv hf'c p).mul (hσc' p k)
  have hGs (p : Fin N) (k : Fin d) : HasCompactSupport (G p k) :=
    (hσs' p k).mul_left
  have hmg (p : Fin N) (k : Fin d) :
      Measurable (Function.uncurry fun ω s => G p k (Y s ω)) :=
    hv.measurable_uncurry_comp (hGc p k).measurable
  have hpg (p : Fin N) (k : Fin d) :
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => G p k (Y s ω) :=
    hv.progressivelyMeasurable_comp (hGc p k)
  have hqg (p : Fin N) (k : Fin d) :=
    compact_energy (P := P) (hGc p k) (hGs p k) Y
  have hito := LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded W ℱ hW hv hℱ0 hnull
    (fun _ => measurable_const)
    (fun p => hv.measurable_uncurry_comp (hbc' p).measurable)
    (fun p => hv.progressivelyMeasurable_comp (hbc' p))
    (fun p => compact_energy (P := P) (hbc' p) (hbs' p) Y)
    hF
    (fun x => (hF.differentiable (by norm_num) x).hasFDerivAt)
    (fun x => (hf'.differentiable (by norm_num) x).hasFDerivAt)
    hmg hpg hqg ht
  have hgen (x : Fin N → ℝ) :
      FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ F x =
        ∑ p, A p x + (1 / 2 : ℝ) * ∑ p, ∑ q, C p q x := by
    have hfirst : f' x (b x) = ∑ p, A p x := by
      rw [LevyStochCalc.apply_eq_sum_coordDeriv]
      apply Finset.sum_congr rfl
      intro p _
      exact mul_comm _ _
    have hsecond : (∑ k, f'' x (σ x k) (σ x k)) =
        ∑ p, ∑ q, C p q x := by
      simp_rw [LevyStochCalc.apply₂_eq_sum_coordDeriv₂]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      dsimp [C]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact congrArg₂ (fun a c : ℝ => a + (1 / 2 : ℝ) * c) hfirst hsecond
  have hAi (p : Fin N) (ω : Ω) :
      IntegrableOn (fun s => A p (Y s ω)) (Set.Ioc (0 : ℝ) T) volume :=
    ((hAc p).comp (hv.continuous_path ω)).integrableOn_Ioc
  have hCi (p q : Fin N) (ω : Ω) :
      IntegrableOn (fun s => C p q (Y s ω)) (Set.Ioc (0 : ℝ) T) volume :=
    ((hCc p q).comp (hv.continuous_path ω)).integrableOn_Ioc
  have hAE (p : Fin N) :
      Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, A p (Y s ω)) P :=
    compact_integral_integrable (hAc p) (hAs p) hv.measurable_uncurry T
  have hCE (p q : Fin N) :
      Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, C p q (Y s ω)) P :=
    compact_integral_integrable (hCc p q) (hCs p q) hv.measurable_uncurry T
  let D : Ω → ℝ :=
    fun ω => ∫ s in Set.Ioc (0 : ℝ) T, FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ F (Y s ω)
  have hD (ω : Ω) :
      D ω = (∑ p, ∫ s in Set.Ioc (0 : ℝ) T, A p (Y s ω)) +
        (1 / 2 : ℝ) * ∑ p, ∑ q, ∫ s in Set.Ioc (0 : ℝ) T, C p q (Y s ω) := by
    dsimp [D]
    simp_rw [hgen]
    rw [integral_add
      (integrable_finsetSum _ fun p _ => hAi p ω)
      ((integrable_finsetSum _ fun p _ =>
        integrable_finsetSum _ fun q _ => hCi p q ω).const_mul _),
      integral_finsetSum _ (fun p _ => hAi p ω), integral_const_mul,
      integral_finsetSum _ (fun p _ =>
        integrable_finsetSum _ fun q _ => hCi p q ω)]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact integral_finsetSum _ fun q _ => hCi p q ω
  have hDi : Integrable D P := by
    have hi := (integrable_finsetSum Finset.univ fun p _ => hAE p).add
      ((integrable_finsetSum Finset.univ fun p _ =>
        integrable_finsetSum Finset.univ fun q _ => hCE p q).const_mul (1 / 2 : ℝ))
    exact hi.congr (Eventually.of_forall fun ω => (hD ω).symm)
  let M : Fin N → Fin d → Ω → ℝ := fun p k =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hW k)
      (fun ω s => G p k (Y s ω)) (hmg p k) (hpg p k) (hqg p k) T
  have hM (p : Fin N) (k : Fin d) :
      Integrable (M p k) P ∧ ∫ ω, M p k ω ∂P = 0 :=
    brownian_integrable_mean_zero (W.W k) ℱ (hW k) _ (hmg p k) (hpg p k)
      (hqg p k) hT
  let S : Ω → ℝ := fun ω => ∑ p, ∑ k, M p k ω
  have hSi : Integrable S P :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun k _ => (hM p k).1
  have hSE : ∫ ω, S ω ∂P = 0 := by
    dsimp [S]
    rw [integral_finsetSum _ (fun p _ =>
      integrable_finsetSum _ fun k _ => (hM p k).1)]
    simp_rw [integral_finsetSum _ (fun k _ => (hM _ k).1)]
    simp only [(hM _ _).2, Finset.sum_const_zero]
  have he : (fun ω => F (Y T ω)) =ᵐ[P] fun ω => F x₀ + D ω + S ω := by
    filter_upwards [hito, h0] with ω hi hz
    change F (Y T ω) - F (Y 0 ω) =
      (∑ p, ∫ s in Set.Ioc (0 : ℝ) T, A p (Y s ω)) + S ω +
        (1 / 2 : ℝ) * ∑ p, ∑ q,
          ∫ s in Set.Ioc (0 : ℝ) T, C p q (Y s ω) at hi
    rw [hz] at hi
    rw [hD]
    linarith
  have hsumI : Integrable (fun ω => F x₀ + D ω) P :=
    (integrable_const (F x₀)).add hDi
  have hFi : Integrable (fun ω => F (Y T ω)) P :=
    (hsumI.add hSi).congr he.symm
  refine ⟨hFi, ?_⟩
  rw [integral_congr_ae he,
    integral_add hsumI hSi,
    integral_add (f := fun _ : Ω => F x₀) (g := D)
      (integrable_const (F x₀)) hDi, hSE]
  simp [D]
