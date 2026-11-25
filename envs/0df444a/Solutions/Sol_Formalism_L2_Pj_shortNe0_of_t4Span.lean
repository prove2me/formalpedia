-- Prove2me | solution 1 for Formalism.L2.Pj.shortNe0_of_t4Span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:46.944354+00:00
-- url     : https://prove2.me/submissions/864cf162-7997-4f26-a6b8-35d035dc562c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort

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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (h : SpanningAtDominantWeight Xo c nab bad nV cusp dδ) : ShortNe0 Xo c nab bad nV dδ cusp := by
  intro a n hd hl hn hc
  by_contra hno
  push Not at hno
  apply hc
  rw [eq_bot_iff]
  intro g hg
  have hsp : Submodule.span c.F (shortGen Xo c nab bad nV a n (dδ n)) = ⊥ :=
    (Submodule.span_eq_bot).2 hno
  have := h a n hd hl hn hg
  rw [hsp] at this
  exact this
end Formalism.L2.Pj
