-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI.gm_homAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:41.465837+00:00
-- url     : https://prove2.me/submissions/e7b6963f-4a13-4b39-b5cf-cf77fc19d37d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_gm_top
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
theorem _root_.solution {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (z : (overAt y.x B).left) (w : Aˣ) :
    gm (homAt y.x f).left z ⊤ (unitΓ w) = gm (𝟙 _) z ⊤ (unitΓ (Units.map f.toMonoidHom w)) := by
  rw [gm_top, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.unitΓ_homAt]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
