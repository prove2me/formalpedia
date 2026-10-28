-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_toLp_gradient_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:40.944246+00:00
-- url     : https://prove2.me/submissions/67c987a8-28bb-400a-b9d9-8fad8c98d624

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
/-- `Γ(f, f) = ‖∇f‖²`: the normalisation of `Γ` carries no extra factor. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_self (f : E → ℝ) (x : E) : gamma f f x = ‖gradient f x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _
variable [FiniteDimensional ℝ E]
end Gamma
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
omit [FiniteDimensional ℝ V] in
/-- The squared `L²(ν)` norm of the class of `∇f` is `∫ ‖∇f‖² dν`. -/
theorem solution {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ‖(FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)‖ ^ 2 =
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f f x ∂(ν : Measure V) := by
  let hG := FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc
  change ‖hG.toLp (gradient f)‖ ^ 2 = ∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f f x ∂(ν : Measure V)
  calc
    ‖hG.toLp (gradient f)‖ ^ 2 =
        ⟪hG.toLp (gradient f), hG.toLp (gradient f)⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, ⟪gradient f x, gradient f x⟫_ℝ ∂(ν : Measure V) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hG] with x hx
      rw [hx]
    _ = ∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f f x ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [FunctionalInequalities.Analysis.BakryEmery.gamma_self]
