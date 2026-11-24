-- Prove2me | solution 1 for Formalism.L2.Pj.nrmC_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:53.877432+00:00
-- url     : https://prove2.me/submissions/e73c40dd-2921-4e62-8611-d329e8e58a57

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {Z : Comp Xo c}
variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
namespace Formalism.L2.Pj
theorem _root_.solution (G : WTZ E) (P : Om Z →+* ℂ) : nrmC fn yP G 0 P = 0 := by
  simp only [nrmC, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero, norm_zero, zero_mul]
end Formalism.L2.Pj
