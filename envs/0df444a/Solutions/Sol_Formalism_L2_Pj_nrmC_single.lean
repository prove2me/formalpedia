-- Prove2me | solution 1 for Formalism.L2.Pj.nrmC_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:44.428232+00:00
-- url     : https://prove2.me/submissions/249cfe3c-380c-415e-b4f3-b7688760fe3c

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
theorem _root_.solution (G : WTZ E) (r : Om Z) (P : Om Z →+* ℂ) :
    nrmC fn yP G (AddMonoidAlgebra.single G r) P = ‖P r‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i) := by
  simp only [nrmC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
end Formalism.L2.Pj
