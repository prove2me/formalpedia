-- Prove2me | solution 1 for CohnElkies.tendsto_stripNormalizedPoissonKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/a3862651-7d1c-4b02-b118-4a219ed6290f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripNormalizedPoissonKernel_eq_extension
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_one
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_continuousAt_one

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    Tendsto (fun σ : ℝ => stripNormalizedPoissonKernel σ T)
      (𝓝[<] 1) (𝓝 (limitingStripPoissonDensity T)) := by
  have hpos : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlt : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 :=
    self_mem_nhdsWithin
  have heq :
      (fun σ : ℝ => stripNormalizedPoissonKernel σ T) =ᶠ[𝓝[<] 1]
        (fun σ : ℝ => stripNormalizedPoissonExtension σ T) := by
    filter_upwards [hpos, hlt] with σ hσpos hσlt
    exact stripNormalizedPoissonKernel_eq_extension
      (by linarith) hσlt T
  have hext :
      Tendsto (fun σ : ℝ => stripNormalizedPoissonExtension σ T)
        (𝓝[<] 1) (𝓝 (limitingStripPoissonDensity T)) := by
    rw [← stripNormalizedPoissonExtension_one T]
    exact (stripNormalizedPoissonExtension_continuousAt_one T).tendsto.mono_left
      nhdsWithin_le_nhds
  exact hext.congr' heq.symm
end CohnElkies
