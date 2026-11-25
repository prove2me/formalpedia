-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.trunc_eG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:47.917935+00:00
-- url     : https://prove2.me/submissions/0f5a5e42-bbd7-411c-be49-bfafaef9dde7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_jetSubstPS_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_jetTrunc_psJet
import Theorems.Thm_Formalism_L2_Pj_isChart_iff
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_corr_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_pullGen_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_val_eL_trunc
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb
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
theorem _root_.solution (C : ChartAt Xo c y) (htr : FrTruncC y C) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
      (ExpGA.eG C φ τ u m) := by
  have hL := Xo.univ.t.PP.isLB
  have hch := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  have hT : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left)
      (eL y C.d C.x C.B.A.act C.e C.wP m) := corr_of_val hL fun z J hJ => by
    rw [val_pull hJ, Category.id_comp]
    exact GermD.val_eL_trunc hch C.e C.wP htr m z J hJ
  have hmor : (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left ≫
      (homAt y.x (jφ φ (m + 1))).left = (homAt y.x (jφ φ m)).left ≫
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp]
    unfold jφ
    rw [jetSubstPS_trunc]
  have hUm : Units.map (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m).toMonoidHom
      (u (m + 1)) = u m :=
    Units.ext ((congrArg _ (hu (m + 1))).trans ((jetTrunc_psJet m _).trans (hu m).symm))
  have hAB : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left)
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
      (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left) := corr_of_val hL fun z J hJ => by
    rw [val_pull hJ, val_pull hJ, val_corr hJ (hτc (m + 1)), Category.id_comp]
    rw [hmor, ← val_pull hJ, val_corr hJ hT, val_pull hJ, Category.id_comp, val_corr hJ (hτc m)]
  have e1 : LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left =
      scaleGenG Xo.univ.t _ _ (unitΓ (u m))
        (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left)
          (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left) := by
    unfold ExpGA.eG
    erw [FBIdLB.pullGen_scaleGenG, FBIdLB.unitΓ_homAt, hUm]
    rfl
  rw [e1]
  exact FBIdLB.corr_scaleGenG Xo.univ.t hAB _
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
