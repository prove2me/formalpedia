-- Prove2me | solution 1 for Formalism.L2.Pj.isChart_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:46.967895+00:00
-- url     : https://prove2.me/submissions/06180618-8118-4c4e-966b-4779960fe5cd

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
namespace Formalism.L2.Pj
theorem _root_.solution (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) :
    IsChart y d F act uvec x ↔ IsChartG Xo.univ.t y.x d F act (fun ℓ => y.u ℓ.1 ℓ.2) uvec x :=
  ⟨fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩,
    fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩⟩
end Formalism.L2.Pj
