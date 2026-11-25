-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ConditionalMainTheorem.landau_zero_free_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:30.722505+00:00
-- url     : https://prove2.me/submissions/d87fe27a-ab74-47d5-87bf-7b41007683ea

import Definitions.Def_Formalism_SizeWindowBrackets_PowerBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_ZetaNonvanishing_RHofHalfPlane
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Theorems.Thm_Formalism_zetaLandau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ConditionalMainTheorem
open Formalism
namespace Formalism.LFunctionChainParameters.ConditionalMainTheorem
theorem _root_.solution : LandauZeroFreeHalfPlane := by
  intro θ h0 h1 y₀ hG s hs
  exact Formalism.zetaLandau 1 (Or.inl rfl) θ h0 h1 ⟨1, y₀, fun y hy => by simpa using hG y hy⟩ s hs
end Formalism.LFunctionChainParameters.ConditionalMainTheorem
