-- Prove2me | solution 1 for Formalism.ZF.riemannZeta_ne_zero_of_mem_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:07.271819+00:00
-- url     : https://prove2.me/submissions/13469cad-bf1c-42b2-9258-870f48e3de2f

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle
import Theorems.Thm_Formalism_ZF_one_sub_div_log_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (c₀ : ℝ)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (c T σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₀) (hT : 0 ≤ T) :
    ∀ w : ℂ, 1 - c / Real.log (T + 2) ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 := by
  intro w h1 _ h3 h4
  exact hZ w h4 ((one_sub_div_log_le c c₀ T w.im hc hcc hT h3).trans h1)
end Formalism.ZF
