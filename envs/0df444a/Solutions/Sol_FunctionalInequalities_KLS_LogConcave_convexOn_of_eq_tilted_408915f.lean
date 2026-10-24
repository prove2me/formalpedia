-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.convexOn_of_eq_tilted_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:49:25.394526+00:00
-- url     : https://prove2.me/submissions/25713c75-898c-4a31-a45b-fd3d17b36c1f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_exp_neg_pos_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_408915f

noncomputable section
open MeasureTheory Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
section Convexity
variable [SecondCountableTopology V] (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- A log-concave law `ν = m.tilted (-U)` with a continuous potential has a convex potential: the
continuous density `e^{-U} / Z` agrees with the log-concave Borell representative of `ν`, which is
continuous because `ν` has full support. Converse of `isBorellDensity_of_eq_tilted`. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) : ConvexOn ℝ Set.univ U := by
  have hint : Integrable (fun x => Real.exp (-U x)) m := FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_408915f hνU
  have hZ : 0 < ∫ y, Real.exp (-U y) ∂m := FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted_408915f hνU
  set Z := ∫ y, Real.exp (-U y) ∂m with hZdef
  set q : V → ℝ := fun x => Real.exp (-U x) / Z with hqdef
  have hqpos : ∀ x, 0 < q x := fun x => div_pos (Real.exp_pos _) hZ
  have hqc : Continuous q := (Real.continuous_exp.comp hU.neg).div_const _
  have hmν : m ≪ (ν : Measure V) := by
    rw [hνU]; exact absolutelyContinuous_tilted (by simpa using hint)
  have hνm : (ν : Measure V) ≪ m := by rw [hνU]; exact tilted_absolutelyContinuous m (-U)
  have hsupp : (ν : Measure V).support = Set.univ := by
    refine Set.eq_univ_of_forall fun x => (Measure.mem_support_iff_forall x).2 fun s hs => ?_
    exact pos_iff_ne_zero.2 fun h0 =>
      (pos_iff_ne_zero.1 (Measure.measure_pos_of_mem_nhds m hs)) (hmν h0)
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m
    (FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_408915f m hνU) hνm
  have hρc : Continuous ρ := by
    have h := hρ.continuousOn_interior_support
    rw [hsupp, interior_univ] at h
    exact continuousOn_univ.mp h
  have hqd : m.withDensity (fun x => ENNReal.ofReal (q x)) = ν := by rw [hνU]; rfl
  have hae : (fun x => ENNReal.ofReal (ρ x)) =ᵐ[m] fun x => ENNReal.ofReal (q x) :=
    (withDensity_eq_iff_of_sigmaFinite hρc.measurable.ennreal_ofReal.aemeasurable
      hqc.measurable.ennreal_ofReal.aemeasurable).mp (hρ.withDensity_eq.trans hqd.symm)
  have hae' : ρ =ᵐ[m] q := by
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hρ.nonneg x) (hqpos x).le).mp hx
  have heq : ρ = q := (hρc.ae_eq_iff_eq m hqc).mp hae'
  have hlog : ∀ x, Real.log (q x) = -U x - Real.log Z := fun x => by
    rw [hqdef, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have h := hρ.logConcave x y a ha (by linarith)
  rw [heq] at h
  have hx' := Real.rpow_pos_of_pos (hqpos x) a
  have hy' := Real.rpow_pos_of_pos (hqpos y) (1 - a)
  have h' := Real.log_le_log (mul_pos hx' hy') h
  rw [Real.log_mul hx'.ne' hy'.ne', Real.log_rpow (hqpos x), Real.log_rpow (hqpos y), hlog, hlog,
    hlog] at h'
  simp only [smul_eq_mul]
  nlinarith
