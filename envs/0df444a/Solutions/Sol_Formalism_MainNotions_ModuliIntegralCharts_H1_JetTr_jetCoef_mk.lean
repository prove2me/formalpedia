-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.jetCoef_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:36.763225+00:00
-- url     : https://prove2.me/submissions/d6a1dfff-e4e3-4df9-a217-afa1614a7781

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
theorem _root_.solution (κ : Type) (m : ℕ) (p : MvPolynomial κ V) :
    jetCoef f κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
