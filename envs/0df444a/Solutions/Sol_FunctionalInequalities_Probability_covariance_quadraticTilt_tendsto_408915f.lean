-- Prove2me | solution 1 for FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:23:50.843166+00:00
-- url     : https://prove2.me/submissions/94d4ff0a-9753-410a-9802-991db4e8b5e0

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_FunctionalInequalities_Probability_inner_covariance_quadraticTilt_tendsto_408915f

noncomputable section
open MeasureTheory Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section Covariance
open ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- **Covariance of the quadratic tilt converges** in operator norm as `δ → 0⁺` (BKL Section 2, p. 5). -/
theorem solution (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) :
    Tendsto (fun δ : ℝ => FunctionalInequalities.Covariance.operator
      ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (FunctionalInequalities.Covariance.operator (μ : Measure E))) := by
  let A : ℝ → E →L[ℝ] E := fun δ => FunctionalInequalities.Covariance.operator
    ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2))
  have h0 : A 0 = FunctionalInequalities.Covariance.operator (μ : Measure E) := by
    dsimp only [A]
    have hw : (fun x : E => -((0 : ℝ) / 2) * ‖x‖ ^ 2) = 0 := by funext x; simp
    rw [hw, tilted_zero]
  have hscalar (u v : E) : ContinuousWithinAt (fun δ => ⟪A δ u, v⟫) (Set.Ioi (0 : ℝ)) 0 := by
    change Tendsto (fun δ => ⟪A δ u, v⟫) (𝓝[>] (0 : ℝ)) (𝓝 ⟪A 0 u, v⟫)
    rw [h0]
    exact FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_408915f μ hμ2 u v
  have hA : ContinuousWithinAt A (Set.Ioi (0 : ℝ)) 0 := by
    apply continuousWithinAt_clm_apply.mpr
    intro u
    let b := stdOrthonormalBasis ℝ E
    rw [b.toBasis.equivFunL.toHomeomorph.isInducing.continuousWithinAt_iff]
    apply continuousWithinAt_pi.mpr
    intro i
    change ContinuousWithinAt (fun δ => b.toBasis.equivFun (A δ u) i) (Set.Ioi (0 : ℝ)) 0
    simpa only [Module.Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, real_inner_comm] using hscalar u (b i)
  change Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 _)
  change Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (A 0)) at hA
  rw [h0] at hA
  exact hA
