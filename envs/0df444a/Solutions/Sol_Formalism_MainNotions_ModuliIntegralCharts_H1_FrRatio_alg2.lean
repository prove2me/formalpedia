-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.alg2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:52.378902+00:00
-- url     : https://prove2.me/submissions/93386343-4326-4d5d-8fae-b3d18be3a520

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution {M : Type} [CommGroup M] (W b0 bs g0 gs : M) (h0 : b0 = W * bs) (h1 : g0 * b0 = W * (gs * bs)) :
    g0 = gs := by
  subst h0
  apply mul_right_cancel (b := W * bs)
  rw [h1, mul_left_comm]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
