-- Prove2me | solution 1 for Formalism.L2.Pj.SaturatedCharts.listProd_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:00.125065+00:00
-- url     : https://prove2.me/submissions/1b59222c-650e-42dd-830c-9032ef7e345e

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
variable {S : Scheme.{0}} {M : Over S} [MonObj M]
namespace Formalism.L2.Pj.SaturatedCharts
theorem _root_.solution {X : Over S} {N : Over S} [MonObj N] (g : M ⟶ N) [IsMonHom g] :
    ∀ {k : ℕ} (u : Fin k → (X ⟶ M)), (List.ofFn u).prod ≫ g = (List.ofFn fun i => u i ≫ g).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.one_comp g
  | k + 1, u => by
    simp only [List.ofFn_succ, List.prod_cons, MonObj.mul_comp]
    rw [solution g (fun i => u i.succ)]
end Formalism.L2.Pj.SaturatedCharts
