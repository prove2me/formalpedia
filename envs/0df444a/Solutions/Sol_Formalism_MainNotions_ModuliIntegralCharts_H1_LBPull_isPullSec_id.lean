-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:41.485699+00:00
-- url     : https://prove2.me/submissions/25356454-bcb2-47c9-aa3f-86fbfc16a1b2

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
theorem _root_.solution {T : Over S0} (hh : 𝟙 (T ⊗ A) ≫ snd T A = snd T A) (s : LB.Sec (LPow A L a T)) :
    IsPullSec A L a (𝟙 (T ⊗ A)) hh s s := by
  intro j
  simp only [Over.id_left, Scheme.Hom.id_app, CommRingCat.id_apply]
  rw [show (homOfLE (chart_le_res A L (𝟙 (T ⊗ A)) hh a j)).op = 𝟙 _ from Subsingleton.elim _ _]
  erw [CategoryTheory.Functor.map_id]
  erw [CommRingCat.hom_id]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
