-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:59.156662+00:00
-- url     : https://prove2.me/submissions/bd158e4e-0566-4143-96b4-c14a5c105a0e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_divLinB_isGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_eta_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_scale_isGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_cube_one_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_exists_ratio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution : ∃ wP : PrimTyG t, IsPrimG t wP := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.prim
  let w1 : PrimTyG t := divLinB t.PP.L _ _ w
  have hw1 : w1.IsGen := divLinB_isGen t.PP.L _ _ w hw
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (eta_one t.G)
    · rfl
  obtain ⟨u, hu⟩ := exists_ratio t.PP.L hL (φ' := fun _ : PUnit => eSec t.G) (ε' := fun _ => 1)
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg, Finset.prod_inv_distrib,
        hpt, Fintype.prod_unique]
      rw [cube_one_left t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w1 (eSec t.G)) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw1 _) t.PP.rig t.PP.rigGen
  have hes : eSec t.G ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
  refine ⟨scaleGenG t _ _ (pullU t.G.hom ⊤ u⁻¹) w1, scale_isGen t _ _ _ w1 hw1, corr_of_val hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((val_scale t _ _ _ _ _ y J hJ).trans ?_)
  refine (congrArg₂ (· * ·) ((gm_pull (𝟙 _ ≫ eSec t.G) t.G.hom y ⊤ trivial u⁻¹).trans
    (congrArg (fun r => gm r y ⊤ u⁻¹) (by rw [Category.assoc, hes, Category.comp_id])))
    ((val_pull hJ w1 _ _).symm.trans (hu _ (𝟙 _) y J hJ))).trans ?_
  rw [map_inv, inv_mul_cancel_left]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
