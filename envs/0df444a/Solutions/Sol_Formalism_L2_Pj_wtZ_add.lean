-- Prove2me | solution 1 for Formalism.L2.Pj.wtZ_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:02.148855+00:00
-- url     : https://prove2.me/submissions/74766ee8-5449-41d3-be73-010cd6106cc6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace Formalism.L2.Pj
theorem _root_.solution {E : Type} [Field E] (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    wtZ (a + a') (n + n') = wtZ a n + wtZ a' n' := by
  unfold wtZ
  ext <;> simp
end Formalism.L2.Pj
