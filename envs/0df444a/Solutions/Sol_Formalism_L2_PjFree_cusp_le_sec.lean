-- Prove2me | solution 1 for Formalism.L2.PjFree.cusp_le_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:04.926425+00:00
-- url     : https://prove2.me/submissions/0683130f-44fa-4270-8d33-a1913c5e67c7

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
namespace Formalism.L2.PjFree
theorem _root_.solution (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left
end Formalism.L2.PjFree
