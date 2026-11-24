-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.germCompOne_identityPoint_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:02.893619+00:00
-- url     : https://prove2.me/submissions/5466444d-46a9-4ad9-863b-336a3b726f0d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
theorem _root_.solution (φ : Pt S 1 d) : comp1 φ (pt S (n := 1) d 0) = φ := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![pt S (n := 1) d 0] p.1 p.2 : MvPowerSeries (Fin 1 × Fin d) S)) (φ i) = φ i
  have hX : (fun p : Fin 1 × Fin d => (![pt S (n := 1) d 0] p.1 p.2 : MvPowerSeries (Fin 1 × Fin d) S)) = MvPowerSeries.X := by
    funext p
    rcases p with ⟨a, c⟩
    rw [Subsingleton.elim a 0]
    rfl
  rw [hX]
  first
  | exact congrFun MvPowerSeries.subst_self _
  | (rw [MvPowerSeries.subst_self]; rfl)
  | (rw [← MvPowerSeries.map_algebraMap_eq_subst_X]; simp)
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
