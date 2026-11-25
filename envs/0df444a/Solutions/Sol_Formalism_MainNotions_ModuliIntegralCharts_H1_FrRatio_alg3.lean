-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.alg3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:50.560102+00:00
-- url     : https://prove2.me/submissions/656f9d88-277a-4efd-8ccb-dbc1dea27e80

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
theorem _root_.solution {M : Type} [CommGroup M] (L W ba bb ga gb : M) (h0 : L * ba = W * bb)
    (h1 : L * (ga * ba) = W * (gb * bb)) : ga = gb := by
  apply mul_right_cancel (b := W * bb)
  calc ga * (W * bb) = ga * (L * ba) := by rw [h0]
    _ = L * (ga * ba) := mul_left_comm _ _ _
    _ = W * (gb * bb) := h1
    _ = gb * (W * bb) := mul_left_comm _ _ _
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
