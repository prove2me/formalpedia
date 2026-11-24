-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.axJ_swJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:56.825804+00:00
-- url     : https://prove2.me/submissions/73337140-1508-4481-99e8-e158b6830dcd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_swJ_X
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_axJ_X

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {S : Type} [CommRing S] (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
theorem _root_.solution (m : ℕ) (b : Bool) : (axJ (S := S) d m b).comp (swJ d m) = axJ d m (!b) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, swJ_X, axJ_X]
  cases b <;> fin_cases k <;> simp [axV]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
