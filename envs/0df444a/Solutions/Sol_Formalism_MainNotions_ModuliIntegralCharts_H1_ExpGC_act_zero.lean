-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.act_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:10.438072+00:00
-- url     : https://prove2.me/submissions/52e446d2-8d6b-4a9e-97af-7931b4a53e5d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
theorem _root_.solution : Xo.univ.t.act.act 0 = 1 := by
  have h := Xo.univ.t.act.add 0 0
  rw [add_zero] at h
  first
    | exact mul_eq_left.mp h.symm
    | exact mul_right_eq_self.mp h.symm
    | exact self_eq_mul_right.mp h
    | simpa using h
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
