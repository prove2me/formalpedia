-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:47.861818+00:00
-- url     : https://prove2.me/submissions/d5a5e9ab-148a-4315-bfb4-af8a3d73b9ea

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
theorem _root_.solution {T T' T'' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {h' : T'' ⊗ A ⟶ T' ⊗ A} {hh' : h' ≫ snd T' A = snd T'' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} {s'' : LB.Sec (LPow A L a T'')}
    (h1 : IsPullSec A L a h hh s s') (h2 : IsPullSec A L a h' hh' s' s'') :
    IsPullSec A L a (h' ≫ h) (by rw [Category.assoc, hh, hh']) s s'' := by
  intro j
  rw [h2 j, h1 j]
  simp only [Over.comp_left, Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE_assoc]
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
