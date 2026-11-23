-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.LFunction_eq_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:15.804032+00:00
-- url     : https://prove2.me/submissions/29499e4c-e300-49a2-a91a-0fb0f8d01734

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_G_differentiableOn
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_LFunction_eq_G_of_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution (hχ : χ ≠ 1) {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = G χ s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (G χ) {s : ℂ | 0 < s.re} := (G_differentiableOn χ hB).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] G χ := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2' : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
      show (1 : ℝ) < (2 : ℂ).re
      norm_num
    filter_upwards [ho.mem_nhds h2'] with z hz
    exact LFunction_eq_G_of_one_lt χ hB hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected h2 hev hs
end Formalism.FX.LFunctionPartialSum
