-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.cgen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:51.699913+00:00
-- url     : https://prove2.me/submissions/da42216c-49a4-41e4-a1eb-da5bc65712c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) :
    (cgen L φ ε j0 h0).IsGen := fun i j => unit_ext fun y hy => by
  have h0y : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j0 := by rw [h0]; trivial
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((gm_linComb L φ ε (𝟙 _) y i j0 hy.1 h0y).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.2 _).trans (gm_linComb L φ ε (𝟙 _) y j j0 hy.2 h0y))))).symm
  exact (trF_trans hL φ ε (𝟙 _) y hy.1 hy.2 h0y).symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
