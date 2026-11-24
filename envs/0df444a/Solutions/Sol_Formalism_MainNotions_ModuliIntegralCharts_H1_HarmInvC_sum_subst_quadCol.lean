-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.sum_subst_quadCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:56.946116+00:00
-- url     : https://prove2.me/submissions/10020efb-5dd3-4421-8fa4-24f48afd55ee

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_subst_quadCol

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
variable {S : Type} [CommRing S] {n d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
theorem _root_.solution (r : S) (β : Matrix (Fin d) (Fin d) S) :
    ∑ b : Fin n, MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) = r • TB.quadCol (n := n) β := by
  simp only [subst_quadCol]
  simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Finset.smul_sum]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
