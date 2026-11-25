-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI.val_eAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:23.059426+00:00
-- url     : https://prove2.me/submissions/eee74d6a-bae3-4bda-8d3c-1c9d7cc01450

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm_one__a_64b806b6d605
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm__L_8c0085973b4b
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_gm_homAt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_val_eG
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (k : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m k) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstP m (actP (Dw := Dw) (S := S) c k)).toMonoidHom (u m))) *
        (val C.wP ((ptm C ![φa c φ k] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φa c φ k, φa c φ (H.w0 * k)] m).left z J) := by
  have hm1 : (𝟙 _ ≫ (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k))).left) ≫ (homAt y.x (jφ φ m)).left =
      (ptm C ![φa c φ k] m).left := by
    rw [Category.id_comp, ← Over.comp_left, ptm_one_φa C φ hφ m k]
  have hm2 : (ptm C ![φa c φ k] m).left ≫ (homAt y.x (jetSubstP m (σL C m))).left =
      (ptm C ![φa c φ k, φa c φ (H.w0 * k)] m).left := by
    rw [← Over.comp_left, ptm_σL C φ hφ hact m k]
  unfold eAt
  rw [val_pull hJ, val_eG C φ τ u m _ z J hJ, val_corr hJ (hτc m), hm1, Category.id_comp, gm_homAt]
  unfold eL
  rw [val_mul hJ, val_pull hJ,
    show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)])
        (ptm C ![φa c φ k] m).left z J =
      val (C.e m) ((ptm C ![φa c φ k] m).left ≫ (homAt y.x (jetSubstP m (σL C m))).left) z J from val_pull hJ _ _ _,
    hm2]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
