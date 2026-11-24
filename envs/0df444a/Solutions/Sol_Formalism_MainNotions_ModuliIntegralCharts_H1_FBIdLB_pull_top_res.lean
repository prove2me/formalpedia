-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.pull_top_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:54.589095+00:00
-- url     : https://prove2.me/submissions/03adbdea-5356-4f7c-862c-cc3f4bfea62a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
theorem _root_.solution (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
