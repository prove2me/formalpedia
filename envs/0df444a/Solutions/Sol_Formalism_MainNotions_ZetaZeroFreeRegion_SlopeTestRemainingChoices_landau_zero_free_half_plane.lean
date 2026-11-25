-- Prove2me | solution 1 for Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices.landau_zero_free_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:29.682482+00:00
-- url     : https://prove2.me/submissions/a8b2f355-4c4e-4763-a198-6b588625b360

import Mathlib
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_LandauZeroFreeHalfPlane
import Theorems.Thm_Formalism_zetaLandau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ZetaZeroFreeRegion Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices
open Formalism
namespace Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices
theorem _root_.solution : LandauZeroFreeHalfPlane := by
  intro θ h0 h1 y₀ hG s hs
  exact Formalism.zetaLandau 1 (Or.inl rfl) θ h0 h1 ⟨1, y₀, fun y hy => by simpa using hG y hy⟩ s hs
end Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices
