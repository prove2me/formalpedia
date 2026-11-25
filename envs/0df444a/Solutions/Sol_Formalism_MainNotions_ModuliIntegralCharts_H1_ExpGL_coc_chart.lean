-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL.coc_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:17:04.398008+00:00
-- url     : https://prove2.me/submissions/5fbf23f8-9a3d-4a5b-affe-9dc71f6f5dd5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocChart
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_genPow__02a5ca4210cb
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_gmU_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_gmU_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_uk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_Bq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_exp_chart_action_point
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_val_eAt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGK_val_e
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_one_6e26593e29be
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
set_option maxHeartbeats 2000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
theorem _root_.solution (hP1 : ExpGJ.PhOneValSt) (hP2 : ExpGJ.PhTwoValSt) (hAd : ExpGJ.AdValSt) (hUid : UnitIdSt)
    (hO : ExpGO.BqOriginSt) (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf C.B.G.F C.uvec φ)
    (hx : IsExpChart y (xExp y C φ))
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))))
    (a : 𝓞 E) (wLa : ExpGC.AdTy Xo a) (hra : ExpGD.AdRel C a wLa) (wLb : ExpGC.AdTy Xo (H.bar a))
    (hrb : ExpGD.AdRel C (H.bar a) wLb) (β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε))
    (hβ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq C.wP a wLa wLb) r z J *
          (val (ExpGC.Bq C.wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m (1 + a * H.bar a))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (xExp y C φ m).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m a) 2)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (ExpGA.eG C φ τ u m)
            (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m (a * H.bar a))))) := by
  have hL := Xo.univ.t.PP.isLB
  have hbb : H.bar (H.bar a) = a := by rw [← hs, ← hs, star_star]
  have hφc := hφ.const
  refine corr_of_val hL fun z J hJ => ?_
  obtain ⟨w1, hw1, e1⟩ := hP1 E H Dw l Xo c S y C φ hφ hx m 1 (a * H.bar a) ((1 + a * H.bar a) * H.w0) z J hJ
  obtain ⟨w2, hw2, e2⟩ := hP2 E H Dw l Xo c S y C φ hφ hx m 1 H.w0 (a * H.bar a * H.w0) z J hJ
  obtain ⟨w3, hw3, e3⟩ := hP2 E H Dw l Xo c S y C φ hφ hx m (a * H.bar a) H.w0 (a * H.bar a * H.w0) z J hJ
  obtain ⟨w4, hw4, e4⟩ := hAd E H Dw l Xo c S y C φ hφ hx hact a wLa hra m 1 (a * H.w0) z J hJ
  obtain ⟨w5, hw5, e5⟩ := hAd E H Dw l Xo c S y C φ hφ hx hact (H.bar a) wLb hrb m a H.w0 z J hJ

  have hmo : (xExp y C φ m).left ≫ (toUnit Xo.univ.t.G).left =
      (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin (dL Dw)) m))).left ≫ (toUnit (overAt y.x S)).left := by
    rw [← Over.comp_left, ← Over.comp_left, toUnit_unique (xExp y C φ m ≫ toUnit _) (toUnit _),
      toUnit_unique (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin (dL Dw)) m)) ≫ toUnit _) (toUnit _)]
  have hmo' : (toUnit (overAt y.x S)).left ≫ eSec Xo.univ.t.G = (1 : overAt y.x S ⟶ Xo.univ.t.G).left := rfl
  have horig : val (ExpGC.Bq C.wP a wLa wLb) ((xExp y C φ m).left ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
      val Xo.univ.t.PP.rig ((xExp y C φ m).left ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ) = 1 := by
    rw [← Category.assoc, hmo, Category.assoc, hmo']
    exact hO E H Dw l Xo c hs S y C a wLa hra wLb hrb _ _ z J hJ

  have hW : ∀ k : 𝓞 E, (xExp y C φ m).left ≫ (Xo.univ.t.act.act k).left = (ptm C ![φa c φ k] m).left ≫ (C.x m).left :=
    fun k => by rw [← Over.comp_left, exp_chart_action_point C φ hφc hx m k, Over.comp_left]
  have hW1 : (xExp y C φ m).left = (ptm C ![φ] m).left ≫ (C.x m).left := by
    unfold xExp
    rw [Over.comp_left, jφ_eq]

  have hUnit : gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a))).toMonoidHom (u m))) *
      gm (𝟙 _) z ⊤ (unitΓ w5) =
      gm (𝟙 _) z ⊤ (unitΓ w1) * gm (𝟙 _) z ⊤ (unitΓ w2) * gm (𝟙 _) z ⊤ (unitΓ w3) * gm (𝟙 _) z ⊤ (unitΓ w4) *
        gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstP m (actP (Dw := Dw) (S := S) c a)).toMonoidHom (u m))) ^ 2 *
        gm (𝟙 _) z ⊤ (unitΓ (u m)) *
        gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a))).toMonoidHom (u m))) := by
    simp only [← gmU_mul, ← gmU_pow]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_uk C φ hφc u hu m, hu m, hw1, hw2, hw3, hw4, hw5, φa_one]
    have hp2 : ∀ f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, psJet m f ^ 2 = psJet m (f ^ 2) := fun f => by
      rw [pow_two, pow_two, FBIdJet.psJet_mul]
    rw [hp2, ← FBIdJet.psJet_mul, ← FBIdJet.psJet_mul, ← FBIdJet.psJet_mul, ← FBIdJet.psJet_mul, ← FBIdJet.psJet_mul,
      ← FBIdJet.psJet_mul, ← FBIdJet.psJet_mul]
    exact congrArg (psJet m) (hUid E H Dw l Xo c hs S y C φ hφ hact a)

  rw [val_eAt C φ hφc hact τ u hτc m _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp, hβ _ _ z J hJ, horig, inv_one,
    _root_.mul_one, val_mul hJ, val_genPow', val_eAt C φ hφc hact τ u hτc m _ z J hJ, val_mul hJ,
    val_e C φ hφc hact τ u hτc m z J hJ, val_eAt C φ hφc hact τ u hτc m _ z J hJ]
  rw [val_Bq C a wLa wLb _ z J hJ, e1, e2, e3, e4, e5, hW, hW, hW, hW1, hbb]
  simp only [φa_one]
  have hU' := eq_mul_inv_of_mul_eq hUnit
  rw [hU']
  ring_nf
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  abel
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
