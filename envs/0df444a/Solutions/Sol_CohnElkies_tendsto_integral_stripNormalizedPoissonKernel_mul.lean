-- Prove2me | solution 1 for CohnElkies.tendsto_integral_stripNormalizedPoissonKernel_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/527cdda6-b6be-4e75-8ede-aed8364a9fed

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripNormalizedPoissonKernel_eq_extension
import Theorems.Thm_CohnElkies_tendsto_stripNormalizedPoissonKernel
import Theorems.Thm_CohnElkies_stripNormalizedPoissonKernel_integrable
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_le_majorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hmajor : Integrable
      (fun T : ℝ => stripPoissonExponentialMajorant T * ‖f T‖)) :
    Tendsto
      (fun σ : ℝ =>
        ∫ T : ℝ, stripNormalizedPoissonKernel σ T * f T)
      (𝓝[<] 1)
      (𝓝 (∫ T : ℝ, limitingStripPoissonDensity T * f T)) := by
  have hpos : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlt : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 :=
    self_mem_nhdsWithin
  apply tendsto_integral_filter_of_dominated_convergence
    (fun T : ℝ => stripPoissonExponentialMajorant T * ‖f T‖)
  · filter_upwards [hpos, hlt] with σ hσpos hσlt
    exact
      (stripNormalizedPoissonKernel_integrable
        (by linarith) hσlt).aestronglyMeasurable.mul hf
  · filter_upwards [hpos, hlt] with σ hσpos hσlt
    filter_upwards [] with T
    have hext := stripNormalizedPoissonKernel_eq_extension
      (by linarith : -1 < σ) hσlt T
    have hbound := stripNormalizedPoissonExtension_le_majorant
      hσpos.le hσlt.le T
    rw [norm_mul, Real.norm_eq_abs, hext,
      abs_of_nonneg hbound.1]
    exact mul_le_mul_of_nonneg_right hbound.2 (norm_nonneg _)
  · exact hmajor
  · filter_upwards [] with T
    exact (tendsto_stripNormalizedPoissonKernel T).mul
      tendsto_const_nhds
end CohnElkies
