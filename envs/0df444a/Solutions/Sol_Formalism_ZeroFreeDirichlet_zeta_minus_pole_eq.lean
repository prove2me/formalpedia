-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zeta_minus_pole_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:13.387724+00:00
-- url     : https://prove2.me/submissions/8f8f3ca4-4a9c-4d22-b294-94a37dcf148c

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqEntire

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
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaSubPole
  exact Function.update_of_ne hs _ _
end Formalism.ZeroFreeDirichlet
