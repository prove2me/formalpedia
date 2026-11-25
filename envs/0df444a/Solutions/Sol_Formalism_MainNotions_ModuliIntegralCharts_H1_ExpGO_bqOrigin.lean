-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO.bqOrigin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:38.113386+00:00
-- url     : https://prove2.me/submissions/281cb10f-8cfb-41a2-af2c-e8c81624cca3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpGOPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_wL_zero
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 800000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
theorem _root_.solution : BqOriginSt := by
  unfold BqOriginSt
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C a wLa hLa wLb hLb Z r z J hJ

  have hA : ∀ e : 𝓞 E, (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act e = 1 := by
    intro e
    haveI := Xo.univ.t.act.hom e
    first
      | (simp; done)
      | (show (toUnit _ ≫ η[Xo.univ.t.G]) ≫ _ = toUnit _ ≫ η[Xo.univ.t.G]
         rw [Category.assoc, IsMonHom.one_hom])

  have hF : lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 = lift 1 (lift 1 1) := by
    first
      | (rw [show faceMap Xo.univ.t.G 2 = lift (x2 Xo.univ.t.G 0)
              (lift (x2 Xo.univ.t.G 1) (pzero Xo.univ.t.G (G2 Xo.univ.t.G))) from rfl,
            comp_lift, comp_lift,
            show x2 Xo.univ.t.G 0 = fst _ _ from rfl, show x2 Xo.univ.t.G 1 = snd _ _ from rfl,
            lift_fst, lift_snd,
            show pzero Xo.univ.t.G (G2 Xo.univ.t.G) = (1 : G2 Xo.univ.t.G ⟶ Xo.univ.t.G) from rfl,
            ExpGD.comp_one'])
      | (simp [faceMap, x2, pzero]; done)

  have hR : val C.wP (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J =
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    rw [← val_corr hJ C.prim.2 (r ≫ (toUnit (overAt y.x S)).left), val_pull hJ, Category.assoc]
    all_goals first | rfl | exact hJ
  have hP : ∀ e : 𝓞 E, val C.wP ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (Xo.univ.t.act.act e).left) z J = val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    intro e
    rw [Category.assoc, ← Over.comp_left, hA, hR]

  have hC : ∀ e₁ e₂ e₃ : 𝓞 E, val Xo.univ.t.cub.t ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃))).left) z J = 1 := by
    intro e₁ e₂ e₃
    have hm : (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫
        lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 := by
      rw [hF, comp_lift, comp_lift, hA, hA, hA]
    rw [Category.assoc, ← Over.comp_left, hm, Over.comp_left, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (Xo.univ.t.cub.face 2) _).trans ?_)
    first | exact val_one _ | exact val_one hJ _ | (simp [val_one, hJ]; done)

  have hLa0 : val wLa ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C a wLa hLa r z J hJ
  have hLb0 : val wLb ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C (H.bar a) wLb hLb r z J hJ

  have hCB : val (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left)))
      (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 := by
    refine (val_mul hJ _ _ _).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    refine (congrArg _ (val_mul hJ _ _ _)).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _),
      show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    simp

  change val (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (1 + a * H.bar a)).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ C.wP)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (a * H.bar a)).left))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act 1))).left)
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act (a * H.bar a)))).left)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left)))))
    (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1
  simp only [val_mul hJ, val_inv, val_pull hJ, hP, hR, hC, hLa0, hLb0, hJ]
  rw [hCB]
  clear hA hF hR hP hC hLa0 hLb0 hstar hLa hLb hCB
  generalize val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J = R
  group
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
