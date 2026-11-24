-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL.val_Bq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:24.268266+00:00
-- url     : https://prove2.me/submissions/7aaff952-8d50-4caa-9660-43ced1a5d18e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
theorem _root_.solution (C : ChartAt Xo c y) (a : 𝓞 E) (wLa : ExpGC.AdTy Xo a) (wLb : ExpGC.AdTy Xo (H.bar a)) {Z : Scheme.{0}}
    (ρ : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGC.Bq C.wP a wLa wLb) ρ z J =
      val C.wP (ρ ≫ (Xo.univ.t.act.act (1 + a * H.bar a)).left) z J *
          ((val C.wP (ρ ≫ (Xo.univ.t.act.act a).left) z J)⁻¹ * (val C.wP (ρ ≫ (Xo.univ.t.act.act a).left) z J)⁻¹) *
          ((val C.wP ρ z J)⁻¹ * (val C.wP (ρ ≫ (Xo.univ.t.act.act (a * H.bar a)).left) z J)⁻¹) *
        ((val (ExpGC.cubAt (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.bar a))
            (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0))) ρ z J *
          (val (ExpGC.cubAt (Xo.univ.t.act.act H.w0) (Xo.univ.t.act.act (a * H.bar a * H.w0)) (Xo.univ.t.act.act 1)) ρ z J *
            val (ExpGC.cubAt (Xo.univ.t.act.act H.w0) (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a))) ρ z J)) *
        (val (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left) ρ z J *
          (val (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left) ρ z J)⁻¹)) := by
  unfold ExpGC.Bq
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg _ (val_pull hJ _ _ _)))
          ((val_inv _ _).trans (congrArg _ (val_pull hJ _ _ _)))))))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
        ((val_inv _ _).trans (congrArg _ (val_pull hJ _ _ _)))))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _)))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))))))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
