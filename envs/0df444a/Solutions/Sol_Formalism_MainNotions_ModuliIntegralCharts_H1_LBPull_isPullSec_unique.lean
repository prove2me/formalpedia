-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isPullSec_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:57.111225+00:00
-- url     : https://prove2.me/submissions/80e2fdf9-0baf-4df3-bacd-e6183b940bf9

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
theorem _root_.solution {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' s'' : LB.Sec (LPow A L a T')}
    (h' : IsPullSec A L a h hh s s') (h'' : IsPullSec A L a h hh s s'') : s' = s'' := by
  obtain ⟨f1, c1⟩ := s'
  obtain ⟨f2, c2⟩ := s''
  have hf : f1 = f2 := funext fun j => (h' j).trans (h'' j).symm
  subst hf
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
