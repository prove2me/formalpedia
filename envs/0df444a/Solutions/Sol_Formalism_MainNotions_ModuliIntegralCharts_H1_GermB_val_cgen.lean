-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_cgen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:47.276285+00:00
-- url     : https://prove2.me/submissions/4ab74381-84e9-4a9a-b0b8-77a205c7cdeb

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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i0 : L.ι) (h0 : LB.wchart L φ (fun _ => i0) = ⊤) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val (cgen L φ ε (fun _ => i0) h0) r z J = ∏ k, cv L i0 z J (r ≫ φ k) ^ ε k :=
  (gm_res r z _ (hJ.mem φ r) _).trans (gm_linComb L φ ε r z _ _ (hJ.mem φ r) (by rw [h0]; trivial))
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
