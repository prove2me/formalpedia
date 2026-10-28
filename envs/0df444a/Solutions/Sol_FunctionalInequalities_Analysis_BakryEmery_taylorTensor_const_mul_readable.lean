-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_const_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:24.62779+00:00
-- url     : https://prove2.me/submissions/dd210197-7443-4d87-9143-06dae95cf090

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `T_d` is homogeneous. -/
theorem solution (μ : Measure E) (c : ℝ) (f : E → ℝ) (d : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => c * f x) d = c • FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d := by
  have hT : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => c * f x) = fun z => c * FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f z := by
    funext z
    simp only [FunctionalInequalities.Analysis.BakryEmery.tiltAverage]
    exact integral_const_mul c _
  unfold FunctionalInequalities.Analysis.BakryEmery.taylorTensor
  rw [hT]
  by_cases hc : c = 0
  · subst hc
    ext h
    simp
  · have key := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ) (f := FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f)
      (x := 0) (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)) (i := d)
    have hfun : (⇑(ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)) ∘ FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f) =
        fun z => c * FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f z := by
      funext z
      simp [ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    rw [hfun] at key
    ext h
    rw [smul_apply, key, smul_apply,
      smul_apply]
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, smul_eq_mul]
    ring
