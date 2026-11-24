-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC.homAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:36.98912+00:00
-- url     : https://prove2.me/submissions/f8c63fc0-015e-44f7-b9c8-7c6103b82b3e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
variable {G x0}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
theorem _root_.solution {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (ψ : A →ₐ[S] B) :
    homAt x0 ψ = (Over.map x0).map (spMap ψ) := by
  first
  | rfl
  | exact Over.OverMorphism.ext rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
