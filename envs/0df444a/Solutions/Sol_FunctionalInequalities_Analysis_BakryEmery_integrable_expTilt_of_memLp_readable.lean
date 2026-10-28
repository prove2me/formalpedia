-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_expTilt_of_memLp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:20.555389+00:00
-- url     : https://prove2.me/submissions/e857ee8d-40e3-4c89-adf0-252b2d522c1b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_readable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- Square-integrable functions are integrable against every exponential tilt of a finite measure
with all exponential moments. -/
theorem solution
    (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → G}
    (hg : MemLp g 2 μ) (z : E) : Integrable g (FunctionalInequalities.Analysis.BakryEmery.expTilt μ z) := by
  have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
  have hez : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
    refine (hexp ‖z‖).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (real_inner_le_norm z x)
  unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
  rw [integrable_tilted_iff hez]
  refine (FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_readable μ hexp hg.norm ‖z‖).mono'
    (hc.aestronglyMeasurable.smul hg.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_norm]
  gcongr
  exact real_inner_le_norm z x
