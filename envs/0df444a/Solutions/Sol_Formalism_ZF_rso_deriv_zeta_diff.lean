-- Prove2me | solution 1 for Formalism.ZF.rso_deriv_zeta_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:08.051805+00:00
-- url     : https://prove2.me/submissions/14a9d675-c243-4d39-b76a-d73f2da38844

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf

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
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} := by
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hd.deriv isOpen_ne
end Formalism.ZF
