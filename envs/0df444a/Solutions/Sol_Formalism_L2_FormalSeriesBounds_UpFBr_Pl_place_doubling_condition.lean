-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.place_doubling_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:28:52.754541+00:00
-- url     : https://prove2.me/submissions/49f4442e-f152-4a6e-83f1-3ac240b1186e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_placeX_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution : PlaceCriterionOfIdempotent := by
  unfold PlaceCriterionOfIdempotent
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl _ d _ em hfrob hsep hε
  obtain ⟨ε, hε1, hε2, hε3⟩ := hε
  exact placeX_of em hl hfrob hsep ε hε1 hε2 hε3
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
