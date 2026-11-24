-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI.val_eG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:45:34.939222+00:00
-- url     : https://prove2.me/submissions/f7a88928-22fc-49a3-a759-e52e1b5787a3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_val_scale__ccfcdc1cfe51
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jO y (dL Dw) m 1).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) r z J = gm r z ⊤ (unitΓ (u m)) * val (τ m) (r ≫ (homAt y.x (jφ φ m)).left) z J := by
  show val (scaleGen (fun _ : Fin 1 => (homAt y.x (jφ φ m)).left ≫ (C.x m).left) (fun _ => (1 : ℤ)) (unitΓ (u m))
    (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left)) r z J = _
  rw [ExpGD.val_scale' _ _ _ _ _ z J hJ, val_pull hJ]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
