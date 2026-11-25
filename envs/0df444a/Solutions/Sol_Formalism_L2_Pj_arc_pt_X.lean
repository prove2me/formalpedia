-- Prove2me | solution 1 for Formalism.L2.Pj.arc_pt_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:29.773778+00:00
-- url     : https://prove2.me/submissions/c407e6ca-1468-4dfa-861f-48d25b00300c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArcPtX
import Theorems.Thm_P2M_Formalism_L2_Pj_arc__X_isUnit_e6fe5ea1e15b

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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace Formalism.L2.Pj
theorem _root_.solution (Dw : Datum H) (K₁ : Type) [Field K₁] (q : Sp (ArcS Dw K₁)) :
    PowerSeries.X ∉ ((spMap (arcι Dw K₁)) q).asIdeal := by
  intro hX
  have h1 : arcι Dw K₁ PowerSeries.X ∈ q.asIdeal := by
    first
      | exact hX
      | (simpa using hX)
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (arcι_X_isUnit Dw K₁))
end Formalism.L2.Pj
