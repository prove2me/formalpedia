-- Prove2me | solution 1 for Formalism.L2.Pj.SaturatedCharts.chartTan_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:59.833986+00:00
-- url     : https://prove2.me/submissions/cfcdcc69-b2a7-402d-9718-e981b7456f0f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds

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
theorem _root_.solution (v : Sp (DualNumber V) ⟶ t.G.left) (h : IsTanAtG t (𝟙 (Sp V)) v) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t v ((h.1).trans (Category.comp_id _))) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom V V V).toRingHom) ≫ v =
    Spec.map (CommRingCat.ofHom (algebraMap V V)) ≫ η[t.G].left
  refine h.2.trans ?_
  show 𝟙 _ ≫ η[t.G].left = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl
end Formalism.L2.Pj.SaturatedCharts
