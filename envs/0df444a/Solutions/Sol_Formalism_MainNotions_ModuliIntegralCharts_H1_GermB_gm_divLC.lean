-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.gm_divLC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:56.149596+00:00
-- url     : https://prove2.me/submissions/58997ee3-2163-4280-9fc5-22be5267860c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (p q : (K → L.ι) × (K' → L.ι)) (y : Y) (hp : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p)
    (hq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q) :
    gm (𝟙 Y) y _ ((LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).g p q) =
      trF φ ε (𝟙 Y) y p.1 q.1 * (trF φ' ε' (𝟙 Y) y p.2 q.2)⁻¹ := by
  have hpq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q := ⟨hp, hq⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hpq _).trans
    (gm_linComb L φ ε (𝟙 _) y p.1 q.1 hp.1 hq.1)) ((map_inv _ _).trans (congrArg _ ((gm_res _ y _ hpq _).trans
      (gm_linComb L φ' ε' (𝟙 _) y p.2 q.2 hp.2 hq.2)))))
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
