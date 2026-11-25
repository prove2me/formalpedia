-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.psTrunc_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:10.707802+00:00
-- url     : https://prove2.me/submissions/7459d5cb-505b-41de-a52f-307e9777b59f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartTransportSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrA

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by
  simp only [psTrunc, map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
