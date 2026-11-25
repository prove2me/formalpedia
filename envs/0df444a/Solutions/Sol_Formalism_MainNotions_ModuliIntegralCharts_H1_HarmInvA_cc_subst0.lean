-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.cc_subst0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:43.95413+00:00
-- url     : https://prove2.me/submissions/9eac50c9-5a2b-462a-8d41-c38e3fa18fd3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA

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
theorem _root_.solution {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {g : MvPowerSeries σ R}
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) = 0 := MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha hg
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
