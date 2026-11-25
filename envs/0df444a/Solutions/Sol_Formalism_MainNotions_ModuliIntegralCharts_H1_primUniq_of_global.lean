-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.primUniq_of_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:09.719819+00:00
-- url     : https://prove2.me/submissions/2aea5eac-595d-4c5b-9fea-cdc58e395b16

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_isAbelianScheme_univ
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_primUniqOfGlobal_holds

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
theorem _root_.solution (hglob : GlobalFnsSt) : PrimUniqSt := fun E _ _ _ H Dw l Xo wP wP' hP hP' =>
  primUniqOfGlobal_holds hglob E H Dw l Xo (isAbelianScheme_univ Xo) wP wP' hP hP'
end Formalism.MainNotions.ModuliIntegralCharts.H1
