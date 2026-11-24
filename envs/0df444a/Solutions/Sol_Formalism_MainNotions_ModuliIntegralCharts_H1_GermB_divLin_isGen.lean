-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.divLin_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:52.269453+00:00
-- url     : https://prove2.me/submissions/0d4ad43c-7fe4-47e9-99ca-985239c399cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_gm_divLC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) (hw : w.IsGen) :
    (divLin L φ ε φ' ε' w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (i ∘ Sum.inl, i ∘ Sum.inr) ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 Y) y _ hij _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (i ∘ Sum.inl, i ∘ Sum.inr)
    (j ∘ Sum.inl, j ∘ Sum.inr))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hij _))))
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (hw'.trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm
  refine congrArg₂ (· * ·) ((gm_divLC L φ ε φ' ε' _ _ y hi hj).trans ?_) rfl
  refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2).symm
  rw [Fintype.prod_sum_type]
  simp only [trF, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
