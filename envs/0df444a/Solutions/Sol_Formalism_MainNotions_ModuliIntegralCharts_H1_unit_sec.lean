-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.unit_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:39.102577+00:00
-- url     : https://prove2.me/submissions/0772bd7b-fa3b-44a0-a43e-5bc6ec28c3b2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {S : Scheme.{0}} : ∃ ι : S ⟶ (𝟙_ (Over S)).left, ι ≫ (𝟙_ (Over S)).hom = 𝟙 S := ⟨(CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left, by
  simpa using Over.w (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S)))⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1
