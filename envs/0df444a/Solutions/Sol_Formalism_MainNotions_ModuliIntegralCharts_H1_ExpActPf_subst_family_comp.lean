-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.subst_family_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:45:12.158748+00:00
-- url     : https://prove2.me/submissions/67ab59d3-da90-47ef-aaa4-245411dfa7b5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpActPf_has_subst_family_of_const

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
theorem _root_.solution {τ : Type} {d : ℕ} {χ : Fin d → MvPowerSeries τ S} {ψ : Pt S 1 d}
    (hχ : ∀ j, constantCoeff (χ j) = 0) (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : PS S 1 d) :
    subst (fam1 χ) (subst (fam1 ψ) g) = subst (fam1 fun j => subst (fam1 χ) (ψ j)) g :=
  subst_comp_subst_apply (has_subst_family_of_const hψ) (has_subst_family_of_const hχ) g
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
