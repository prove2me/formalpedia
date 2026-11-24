-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.mulGen_scaleGenG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:32.92533+00:00
-- url     : https://prove2.me/submissions/3913406a-7b19-440c-8bdc-bf4d588d185d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_res_top_mul

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
theorem _root_.solution (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
