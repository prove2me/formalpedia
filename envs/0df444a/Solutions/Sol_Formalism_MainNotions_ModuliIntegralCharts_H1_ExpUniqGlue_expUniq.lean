-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.expUniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:10.963859+00:00
-- url     : https://prove2.me/submissions/bd0f45c4-8fef-4be1-950f-6c2eb768d24b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_expUniqRaw

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution : ExpUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y d x x' hx hx' ht
  exact expUniqRaw E H Dw l Xo S y.x d x x' hx hx' ht
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
