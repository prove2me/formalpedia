-- Prove2me | solution 1 for Formalism.L2.Pj.isFrame_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:01.202716+00:00
-- url     : https://prove2.me/submissions/4f79f006-1b70-414b-9728-92b69363c003

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff

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
open MvPolynomial (X C)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
set_option maxHeartbeats 1000000
namespace Formalism.L2.Pj
theorem _root_.solution (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTy y d x m) :
    IsFrame y d x F act ph1 ph2 sy ad e ↔ IsFrameG Xo.univ.t y.x d x F act ph1 ph2 sy ad e :=
  ⟨fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩, fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩⟩
end Formalism.L2.Pj
