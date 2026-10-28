-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:11.897988+00:00
-- url     : https://prove2.me/submissions/8b82ee2c-1e3a-4faf-9c8e-a590a4a00b10

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_readable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
/-- `T_d` is additive on `L²(μ)`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f g : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (d : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => f x + g x) d = FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d + FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ g d := by
  have hint : ∀ φ : E → ℝ, MemLp φ 2 μ → ∀ z : E, Integrable φ (FunctionalInequalities.Analysis.BakryEmery.expTilt μ z) := by
    intro φ hφ z
    have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
    have hez : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      refine (hexp ‖z‖).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (real_inner_le_norm z x)
    unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
    rw [integrable_tilted_iff hez]
    refine (FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_readable μ hexp hφ ‖z‖).mono'
      (hc.aestronglyMeasurable.mul hφ.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    exact real_inner_le_norm z x
  have hsum : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => f x + g x) = FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f + FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ g := by
    funext z
    simp only [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, Pi.add_apply]
    exact integral_add (hint f hf z) (hint g hg z)
  unfold FunctionalInequalities.Analysis.BakryEmery.taylorTensor
  rw [hsum, iteratedFDeriv_add_apply
    ((FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_readable μ hexp hf).contDiffAt.of_le (by exact_mod_cast le_top))
    ((FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_readable μ hexp hg).contDiffAt.of_le (by exact_mod_cast le_top)),
    smul_add]
