-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.ptSecT_whisker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:31.855826+00:00
-- url     : https://prove2.me/submissions/82fce0b5-5c97-46a1-8325-1c6cea191f90

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
theorem _root_.solution {T T' : Over S0} (h : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (h ≫ z)).left ≫ (h ▷ A).left = h.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (h ≫ z) ≫ (h ▷ A) = h ≫ ptSecT A z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e2 := congrArg (fun f => f.left) e
  simpa using e2
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
