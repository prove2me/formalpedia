-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_center_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:27.804013+00:00
-- url     : https://prove2.me/submissions/c9dd26a1-4da5-4809-b6aa-c5a3ad087eb2

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_expTilt_of_memLp_readable

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
omit [BorelSpace E] in
/-- Taylor tensors only see the `μ`-class of a function. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]
end CompleteSpace
end NormedSpace
end ScalarLp
end Lp
end
end
end

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.isProbabilityMeasure_expTilt
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) (z : V) :
    IsProbabilityMeasure (expTilt (ν : Measure V) z) := by
  apply isProbabilityMeasure_tilted
  refine (hexp ‖z‖).mono'
    (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.iteratedFDeriv_sub_const' (F : V → ℝ) (c : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    iteratedFDeriv ℝ d (fun x => F x - c) = iteratedFDeriv ℝ d F := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  funext x
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_sub_const]
omit [FiniteDimensional ℝ V] in
/-- Taylor tensors of degree `d ≥ 1` do not see centering: `T_d(u - ∫u) = T_d u`. -/
theorem solution
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (u : Lp ℝ 2 (ν : Measure V)) {d : ℕ} (hd : 1 ≤ d) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.L2.center ν u)) d = FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑u) d := by
  rw [FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae _ (FunctionalInequalities.L2.center_coeFn ν u) d]
  have havg : FunctionalInequalities.Analysis.BakryEmery.tiltAverage (ν : Measure V) (fun x => u x - FunctionalInequalities.L2.mean ν u) =
      fun z => FunctionalInequalities.Analysis.BakryEmery.tiltAverage (ν : Measure V) (⇑u) z - FunctionalInequalities.L2.mean ν u := by
    funext z
    have := FunctionalInequalities.KLS.LogConcave.PoissonIterate.isProbabilityMeasure_expTilt hexp z
    simp only [FunctionalInequalities.Analysis.BakryEmery.tiltAverage]
    rw [integral_sub (FunctionalInequalities.Analysis.BakryEmery.integrable_expTilt_of_memLp_readable _ hexp (Lp.memLp u) z) (integrable_const _),
      integral_const]
    simp
  unfold FunctionalInequalities.Analysis.BakryEmery.taylorTensor
  rw [havg, FunctionalInequalities.KLS.LogConcave.PoissonIterate.iteratedFDeriv_sub_const' _ _ hd]
