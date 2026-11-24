-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.val_rigPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:16.927664+00:00
-- url     : https://prove2.me/submissions/77cbd5d7-56b0-4009-9cb4-a19eb66340f8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
theorem _root_.solution {Z : Scheme.{0}} (k : ℤ) (r : Z ⟶ (𝟙_ (Over Xo.X)).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) :
    val (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig k) r z J = val Xo.univ.t.PP.rig r z J ^ k := by
  unfold rigPow val
  exact map_zpow _ _ _
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
