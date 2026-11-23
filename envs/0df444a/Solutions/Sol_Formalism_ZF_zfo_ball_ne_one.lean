-- Prove2me | solution 1 for Formalism.ZF.zfo_ball_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:10.456151+00:00
-- url     : https://prove2.me/submissions/7dcc9a11-f48e-455f-a59c-573a62e317dd

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Theorems.Thm_Formalism_ZF_zfo_ball_facts

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
theorem _root_.solution {σ τ : ℝ} (hτ : 3 ≤ |τ|) {w : ℂ}
    (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) : w ≠ 1 ∧ 5 / 2 ≤ |w.im| := by
  obtain ⟨-, him, -⟩ := zfo_ball_facts hw
  have h : 5 / 2 ≤ |w.im| := by
    have h' := abs_sub_abs_le_abs_sub τ w.im
    rw [abs_sub_comm] at h'
    linarith
  refine ⟨fun h1 => ?_, h⟩
  norm_num [h1] at h
end Formalism.ZF
