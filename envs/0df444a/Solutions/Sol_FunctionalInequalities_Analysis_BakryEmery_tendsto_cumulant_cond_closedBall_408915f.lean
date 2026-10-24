-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:52:21.502334+00:00
-- url     : https://prove2.me/submissions/25e41936-df51-42a7-9469-352c8cb84173

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_eq_taylorComp_cond_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tendsto_iteratedFDeriv_laplace_cond_closedBall_408915f

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ᶠ R : ℕ in atTop, ν (Metric.closedBall (0 : E) R) ≠ 0 := by
  have hmono : Monotone fun R : ℕ => Metric.closedBall (0 : E) (R : ℝ) := fun m n hmn =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hB : Tendsto (fun R : ℕ => ν (Metric.closedBall (0 : E) R)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [Metric.iUnion_closedBall_nat, measure_univ] at this
  filter_upwards [hB.eventually (lt_mem_nhds (zero_lt_one' ENNReal))] with R hR
  exact hR.ne'
end CondHelpers
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Cumulants of ball truncations converge** (BKL arXiv:2610.05474v1, p. 19, reduction to compactly
supported laws): for a probability measure with one exponential moment `∫ e^{r‖x‖} < ∞` (`r > 0`, as
given by Borell's lemma for log-concave laws), the cumulants of the conditional laws on the balls
`B(0, R)` converge to those of the measure as `R → ∞`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (k : ℕ) :
    Tendsto (fun R : ℕ => FunctionalInequalities.Analysis.BakryEmery.cumulant (ν[|Metric.closedBall (0 : E) R]) k) atTop
      (𝓝 (FunctionalInequalities.Analysis.BakryEmery.cumulant ν k)) := by
  have h0 : (0 : E) ∈ Metric.ball (0 : E) r := Metric.mem_ball_self hr
  set q : FormalMultilinearSeries ℝ ℝ ℝ := ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1 with hq
  set p : ℕ → FormalMultilinearSeries ℝ E ℝ := fun R =>
    ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R]))
      (Metric.ball 0 r) 0 with hp
  set p' : FormalMultilinearSeries ℝ E ℝ :=
    ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) (Metric.ball 0 r) 0 with hp'
  have hcum : ∀ᶠ R : ℕ in atTop,
      FunctionalInequalities.Analysis.BakryEmery.cumulant (ν[|Metric.closedBall (0 : E) R]) k = q.taylorComp (p R) k := by
    filter_upwards [FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond ν] with R hR
    have : IsProbabilityMeasure (ν[|Metric.closedBall (0 : E) R]) := cond_isProbabilityMeasure hR
    have hexp' : Integrable (fun x => Real.exp (r * ‖x‖)) (ν[|Metric.closedBall (0 : E) R]) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    exact FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_408915f (ν[|Metric.closedBall (0 : E) R]) hr hexp' k
  have hlim : ∀ j : ℕ, Tendsto (fun R => p R j) atTop (𝓝 (p' j)) := by
    intro j
    have := FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall_408915f ν hr hexp j
    simp only [hp, hp', ftaylorSeriesWithin]
    simp only [iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball h0]
    exact this
  rw [FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_408915f ν hr hexp k]
  have hlittle := FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO (l := atTop)
    (p₁ := fun _ : ℕ => q) (p₂ := fun _ : ℕ => q) (q₁ := p) (q₂ := fun _ : ℕ => p')
    (f := fun _ : ℕ => (1 : ℝ)) (n := k)
    (fun j _ => isBoundedUnder_const)
    (fun j _ => by simp)
    (fun j _ => (hlim j).norm.isBoundedUnder_le)
    (fun j _ => isBoundedUnder_const)
    (fun j _ => (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 (hlim j)))
  rw [Asymptotics.isLittleO_one_iff] at hlittle
  exact (tendsto_sub_nhds_zero_iff.1 hlittle).congr' (hcum.mono fun R h => h.symm)
