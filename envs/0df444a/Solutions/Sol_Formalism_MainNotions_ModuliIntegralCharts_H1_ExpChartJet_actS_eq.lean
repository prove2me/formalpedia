-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.actS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:45:21.896843+00:00
-- url     : https://prove2.me/submissions/b86b12ed-e518-4ad8-b2f5-b5d34ea7461e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (a : 𝓞 E) :
    (fun q : Fin 1 × Fin (dL Dw) => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) •
      (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) =
      fun q => ((actP (Dw := Dw) (S := S) c a q : MvPolynomial _ S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) := by
  funext q
  unfold actP
  rw [MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  first
  | rw [MvPowerSeries.smul_eq_C_mul]
  | (rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_self])
  | (ext e; simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_smul])
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
