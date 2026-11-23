-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf.corr_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:11.604957+00:00
-- url     : https://prove2.me/submissions/47f38fdb-4666-4e93-a989-76151c0ceb56

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrPfA

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {X Y : Scheme.{0}} {K : Type} [Fintype K]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
theorem _root_.solution (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen.Corr L φ ε φ ε c c := by
  intro j j' _ _ h
  obtain rfl : j = j' := funext fun k => h k k rfl
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
