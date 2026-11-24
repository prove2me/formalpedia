-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.subst_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:01.721533+00:00
-- url     : https://prove2.me/submissions/453c9dd2-4fcc-417b-883e-6f87f4953aa0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
theorem _root_.solution {σ τ : Type} [Finite σ] [Algebra ℚ R] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (g : MvPowerSeries σ R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst a (PowerSeries.subst g (PowerSeries.exp R)) =
      PowerSeries.subst (MvPowerSeries.subst a g) (PowerSeries.exp R) := by
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hg
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
