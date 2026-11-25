-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.rig_eG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:45.276955+00:00
-- url     : https://prove2.me/submissions/a0f62972-4da1-4853-8e2a-ff14f3663f39

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_aug_comp_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_psJet_zero_of
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_const_compL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_const_expS_neg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGA_const_hL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u 0)
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := by
  have hL := Xo.univ.t.PP.isLB
  have hu0 : u 0 = 1 := Units.ext ((hu 0).trans (psJet_zero_of _ (const_expS_neg _
    (by rw [const_compL φ hφ]; exact ExpGA.const_hL C))))
  have hmor : ((homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left ≫
      (homAt y.x (jφ φ 0)).left) = (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left := by
    rw [← Over.comp_left, homAt_comp, aug_comp_eq]
  refine corr_of_val hL fun z J hJ => ?_
  calc val (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) (𝟙 _) z J
      = val (ExpGA.eG C φ τ u 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z J :=
        val_pull hJ _ _ _
    _ = gm (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z ⊤ (unitΓ (u 0)) *
          val (LB.pullGen Xo.univ.t.PP.L _ _ (τ 0) (homAt y.x (jφ φ 0)).left)
            (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z J :=
        GermB.val_scale Xo.univ.t _ _ _ _ _ z J hJ
    _ = val (τ 0) ((𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) ≫
          (homAt y.x (jφ φ 0)).left) z J := by
        rw [hu0, show unitΓ (1 : (Jet S (Fin 1 × Fin (dL Dw)) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
          _root_.one_mul]
        exact val_pull hJ _ _ _
    _ = val (eL y C.d C.x C.B.A.act C.e C.wP 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
          z J := by
        rw [val_corr hJ (hτc 0), Category.id_comp, Category.id_comp, hmor]
    _ = val (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) (𝟙 _) z J :=
        (val_pull hJ _ _ _).symm.trans (val_corr hJ C.rig0 _)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
