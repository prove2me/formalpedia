-- Prove2me | solution 1 for Formalism.L2.Pj.SaturatedCharts.combAt_of_prodPts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:52:00.96598+00:00
-- url     : https://prove2.me/submissions/af526fd0-3f7b-4ff9-a3cf-9ce4b003e984

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Theorems.Thm_Formalism_L2_Pj_SaturatedCharts_comp_listProd

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.SaturatedCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
variable (t : SAB H (Sp V))
namespace Formalism.L2.Pj.SaturatedCharts
theorem _root_.solution {m : ℕ} (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left))
    (hv : ∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (he : toT t w hw = ReciprocityTheory.ChartRestriction.G.Chart.prodPts a (fun i => toT t (v i) (hv i))) :
    IsCombAtG t (𝟙 (Sp V)) v a w := by
  refine ⟨fun i => eT' ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫ toT t (v i) (hv i),
    fun i => ?_, ?_⟩
  · simp only [Over.comp_left, eT', Over.homMk_left, Category.id_comp, toT]
    rfl
  · rw [← comp_listProd eT' (fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫
      toT t (v i) (hv i))]
    have he' : (List.ofFn fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫
        toT t (v i) (hv i)).prod = toT t w hw := he.symm
    rw [he']
    simp [eT', toT]
end Formalism.L2.Pj.SaturatedCharts
