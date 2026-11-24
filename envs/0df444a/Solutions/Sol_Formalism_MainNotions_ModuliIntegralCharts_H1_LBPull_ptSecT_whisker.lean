-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.ptSecT_whisker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:57.852062+00:00
-- url     : https://prove2.me/submissions/3598a92a-f71a-4be8-9b43-ace98c316889

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
theorem _root_.solution {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (g ≫ z)).left ≫ (g ▷ A).left = g.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (g ≫ z) ≫ (g ▷ A) = g ≫ ptSecT A z := by
    unfold ptSecT
    ext <;> simp
  have e' := congrArg CommaMorphism.left e
  simpa using e'
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
