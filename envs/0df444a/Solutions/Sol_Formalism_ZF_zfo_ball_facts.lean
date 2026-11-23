-- Prove2me | solution 1 for Formalism.ZF.zfo_ball_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:04.373488+00:00
-- url     : https://prove2.me/submissions/562affff-a945-4e0f-b68e-7239c378c220

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {σ τ : ℝ} {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    |w.re - σ| ≤ 1 / 2 ∧ |w.im - τ| ≤ 1 / 2 ∧ ‖w‖ ≤ |σ| + |τ| + 1 / 2 := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre : (w - ((σ : ℂ) + τ * I)).re = w.re - σ := by simp
  have him : (w - ((σ : ℂ) + τ * I)).im = w.im - τ := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← hre]
    exact (Complex.abs_re_le_norm _).trans hw
  · rw [← him]
    exact (Complex.abs_im_le_norm _).trans hw
  · have hc : ‖(σ : ℂ) + τ * I‖ ≤ |σ| + |τ| := by
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real]
    calc ‖w‖ = ‖(w - ((σ : ℂ) + τ * I)) + ((σ : ℂ) + τ * I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - ((σ : ℂ) + τ * I)‖ + ‖(σ : ℂ) + τ * I‖ := norm_add_le _ _
      _ ≤ 1 / 2 + (|σ| + |τ|) := add_le_add hw hc
      _ = |σ| + |τ| + 1 / 2 := by ring
end Formalism.ZF
