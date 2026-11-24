-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:33.792869+00:00
-- url     : https://prove2.me/submissions/1c0f43c8-4f0a-4edc-a1a6-db040daf712d

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
theorem _root_.solution (j : W →+* O) (θ w : O) (f0 f1 ϖ : W) (hθ : θ ^ 2 + j f1 * θ + j f0 = 0)
    (hw : w ^ 2 = j ϖ) (t s : W × W × W × W) :
    pbE j θ w t * pbE j θ w s = pbE j θ w (pbM f0 f1 ϖ t s) := by
  simp only [pbE, pbM, map_add, map_sub, map_mul]
  linear_combination (j t.2.2.1 * j s.2.2.1 + (j t.2.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.2.1) * θ +
      j t.2.2.2 * j s.2.2.2 * θ ^ 2) * hw +
    (j t.2.1 * j s.2.1 + (j t.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.1) * w +
      j t.2.2.2 * j s.2.2.2 * j ϖ) * hθ
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
