-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.rename_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:56.354176+00:00
-- url     : https://prove2.me/submissions/f8333323-6c7d-44d0-9100-94f1977f4041

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC

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
theorem _root_.solution (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) F = MvPowerSeries.subst (sb b) F := by
  first
  | exact MvPowerSeries.rename_eq_subst _ _
  | exact (MvPowerSeries.subst_X_comp_eq_rename _ _).symm
  | (rw [MvPowerSeries.rename_eq_subst]; rfl)
  | (rw [← MvPowerSeries.subst_eq_rename]; rfl)
  | (rw [MvPowerSeries.subst_eq_rename]; rfl)
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
