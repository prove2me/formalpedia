-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:29.02259+00:00
-- url     : https://prove2.me/submissions/b6f993ca-332e-40b6-8a13-147f1e5529ee

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_eta_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_scale_isGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_cube_one_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_cube_one_right
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_divLin_isGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
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
theorem _root_.solution (a : 𝓞 E) : ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1 := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.adj a
  let w2 := divLin t.PP.L (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cε 2)
    (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) (cε 2) w
  have hw2 : w2.IsGen := divLin_isGen t.PP.L _ _ _ _ w hw
  have hp1 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act (H.bar a)] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ fst t.G t.G = 1
      exact (lift_fst _ _).trans (eta_one t.G)
    · show zz t ≫ (snd t.G t.G ≫ t.act.act (H.bar a)) = η[t.G] ≫ t.act.act (H.bar a)
      exact lift_snd_assoc _ _ _
  have hp2 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I =
      (psum t.G ![η[t.G] ≫ t.act.act a, 1] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ (fst t.G t.G ≫ t.act.act a) = η[t.G] ≫ t.act.act a
      exact lift_fst_assoc _ _ _
    · show zz t ≫ snd t.G t.G = 1
      exact (lift_snd _ _).trans (eta_one t.G)
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hp1, hp2, Fintype.prod_empty]
      rw [cube_one_left t (fun p => h p.left), cube_one_right t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w2 (zz t).left) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw2 _)
  have le : (⊤ : ((𝟙_ (Over X0)).left).Opens) ≤ LB.wchart t.PP.L (PEmpty.elim : PEmpty → (_ ⟶ t.G.left)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let u := res le (s.s PEmpty.elim)
  have hz : (zz t).left ≫ (t.G ⊗ t.G).hom = 𝟙 _ := Over.w (zz t)
  refine ⟨scaleGenG t _ _ (pullU (t.G ⊗ t.G).hom ⊤ u⁻¹) w2, scale_isGen t _ _ _ w2 hw2, fun Z r z J hJ => ?_⟩
  refine (val_scale t _ _ _ _ _ z J hJ).trans ?_
  have e1 : val w2 (r ≫ (zz t).left) z J = gm r z ⊤ u := by
    refine (val_pull hJ w2 _ _).symm.trans ((hv Z r z J hJ).symm.trans ?_)
    rw [val_of s r z J PEmpty.elim (fun k => k.elim)]
    exact (gm_res r z le trivial _).symm
  refine (congrArg₂ (· * ·) ((gm_pull (r ≫ (zz t).left) (t.G ⊗ t.G).hom z ⊤ trivial u⁻¹).trans
    (congrArg (fun q => gm q z ⊤ u⁻¹) (by rw [Category.assoc, hz, Category.comp_id]))) e1).trans ?_
  rw [map_inv, inv_mul_cancel]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
