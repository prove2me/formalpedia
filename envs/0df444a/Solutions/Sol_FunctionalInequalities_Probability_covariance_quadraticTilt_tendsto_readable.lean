-- Prove2me | solution 1 for FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:48.371518+00:00
-- url     : https://prove2.me/submissions/8a347e8a-2a68-4fbd-b360-0cdf850fcf6b

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt
import Theorems.Thm_FunctionalInequalities_Probability_inner_covariance_quadraticTilt_tendsto_readable

noncomputable section
open MeasureTheory Filter Topology Set
section Covariance
open ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
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
    exact FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_readable μ hμ2 u v
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
