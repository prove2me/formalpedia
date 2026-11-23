-- Prove2me | solution 1 for Formalism.ZF.zfo_diff_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:06.726631+00:00
-- url     : https://prove2.me/submissions/148869a1-9c85-4719-8dbb-75234c7e345a

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Theorems.Thm_Formalism_ZF_zfo_ball_ne_one

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
theorem _root_.solution {σ τ : ℝ} (hτ : 3 ≤ |τ|) :
    DifferentiableOn ℂ riemannZeta (closedBall ((σ : ℂ) + τ * I) (1 / 2)) := by
  intro w hw
  exact (differentiableAt_riemannZeta (zfo_ball_ne_one hτ hw).1).differentiableWithinAt
end Formalism.ZF
