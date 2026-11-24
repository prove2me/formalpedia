-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.divLinB_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:55.308797+00:00
-- url     : https://prove2.me/submissions/fbc92b6b-c4fb-4ebf-9bd3-89fd9c03c296

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) (hw : w.IsGen) :
    (divLinB L φ ε w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : Fin 1 ⊕ K → L.ι, LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 X : X ⟶ X) y ∈ (LB.div (LB.LinComb L φ ε) L).U (i ∘ Sum.inr, i (Sum.inl 0)) ⊓
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 X) y _ hij _).symm.trans ((congrArg (gm (𝟙 X) y _) (hw (i ∘ Sum.inr, i (Sum.inl 0))
    (j ∘ Sum.inr, j (Sum.inl 0)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 X) y _ hij _))))
  have hg : gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))) =
      (gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j))⁻¹ := by
    refine (map_mul _ _ _).trans ?_
    refine Eq.trans (congrArg₂ (· * ·) ((gm_res _ y _ hij _).trans (gm_linComb L φ ε (𝟙 _) y _ _ hi.1 hj.1))
      ((map_inv _ _).trans (congrArg _ (gm_res _ y _ hij _)))) ?_
    refine Eq.trans ?_ (congrArg _ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2)).symm
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
      Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
    rfl
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((map_inv _ _).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans
    ((gm_res _ y _ hy.2 _).trans (map_inv _ _))))).symm
  exact (congrArg (·⁻¹) (hw'.trans (congrArg (· * _) hg))).trans
    (by simp only [mul_inv_rev, inv_inv]; exact _root_.mul_comm _ _)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
