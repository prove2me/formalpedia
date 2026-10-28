-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.inner_exp_weights_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:09.28305+00:00
-- url     : https://prove2.me/submissions/e5ea165b-f530-4e18-abc8-64e96e6c21fa

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
  intro t ht
  simp only [norm_one, mul_one]
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))
theorem solution {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u : E) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖⟪u, x⟫‖) μ := by
  intro t ht
  have h := (FunctionalInequalities.Analysis.BakryEmery.weightedExpD_integrable_lt (g := fun _ : E => (1 : ℝ))
    measurable_const.aestronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp)) t ht
  refine (h.const_mul ‖u‖).mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [FunctionalInequalities.Analysis.BakryEmery.weightedExpD, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
    norm_one, mul_one]
  calc
    Real.exp (t * ‖x‖) * ‖⟪u, x⟫‖ ≤ Real.exp (t * ‖x‖) * (‖u‖ * ‖x‖) := by
      gcongr
      exact norm_inner_le_norm u x
    _ = ‖u‖ * (Real.exp (t * ‖x‖) * ‖x‖) := by ring
