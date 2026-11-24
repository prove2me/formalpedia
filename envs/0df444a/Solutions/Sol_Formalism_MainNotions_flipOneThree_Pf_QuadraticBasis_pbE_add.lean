-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:46.111135+00:00
-- url     : https://prove2.me/submissions/537b4697-385b-41cc-942c-99ae9bd2ae44

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [CommRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution (j : W →+* O) (θ w : O) (t s : W × W × W × W) :
    pbE j θ w t + pbE j θ w s = pbE j θ w (t + s) := by
  simp only [pbE, Prod.fst_add, Prod.snd_add, map_add]
  ring
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
