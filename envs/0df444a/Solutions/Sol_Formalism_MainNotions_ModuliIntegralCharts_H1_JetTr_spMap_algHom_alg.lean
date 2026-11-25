-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.spMap_algHom_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:58.475803+00:00
-- url     : https://prove2.me/submissions/d1f5d2f1-2996-4704-91f9-31fee7a61254

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : spMap (φ : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  first
  | (rw [← spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (rw [spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
  | unfold spMap
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
