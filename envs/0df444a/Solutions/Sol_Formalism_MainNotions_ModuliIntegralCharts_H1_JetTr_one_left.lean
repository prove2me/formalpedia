-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.one_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:38:52.548322+00:00
-- url     : https://prove2.me/submissions/383c8a1a-907f-4e02-8642-09d94bb2c33d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution {S : Scheme.{0}} {X : Over S} {G : Over S} [MonObj G] :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
