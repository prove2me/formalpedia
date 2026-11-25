-- Prove2me | solution 1 for Deduction.zeroFree_of_rpow_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:28:42.4445+00:00
-- url     : https://prove2.me/submissions/cde98059-2f2d-498a-ab38-ac6cbf852967

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_lemmaL
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_WindowHypOfRpow
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ZeroFreeOfRpowWindow
import Theorems.Thm_Deduction_lemmaL
import Theorems.Thm_Deduction_windowHyp_of_rpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ :=
  lemmaL F hθ hθ1 hδ (windowHyp_of_rpow F hδ h)
end Deduction
