-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.second_axis_at_first_copy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:21.950481+00:00
-- url     : https://prove2.me/submissions/b16766c2-3479-48f6-bac1-11f692230b04

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
variable (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution (m : ℕ) : (axis1 (S := S) d m).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id S _ := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
