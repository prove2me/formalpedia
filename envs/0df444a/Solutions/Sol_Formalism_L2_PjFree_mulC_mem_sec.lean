-- Prove2me | solution 1 for Formalism.L2.PjFree.mulC_mem_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:23.957649+00:00
-- url     : https://prove2.me/submissions/6619aac9-2912-479d-9077-2da7abefc380

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Theorems.Thm_Formalism_L2_Pj_sec_mul


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
theorem _root_.solution (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := sec_mul Xo c a a' n n' hf hg
end Formalism.L2.PjFree
