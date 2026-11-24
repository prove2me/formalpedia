-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.hasSubst0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:03.569804+00:00
-- url     : https://prove2.me/submissions/aa254cb0-58a7-4e9a-9a95-e820f266d9ed

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
theorem _root_.solution {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
