-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD.wL_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:22.073323+00:00
-- url     : https://prove2.me/submissions/b3c8f0be-9762-45a4-bae5-b3f5301bcf9b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_jet_zero_hom_ext
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_val_scale__ccfcdc1cfe51
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_jet_point_zero_eq_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_const_ad
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_psJet_zero_of
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
theorem _root_.solution (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) (hrel : AdRel C a wL) {Z : Scheme.{0}}
    (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
    (hJ : Good Xo.univ.t.PP.L z J) :
    val wL (r ≫ (lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G)).left) z J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel 0
  have hu1 : u = 1 := Units.ext (hu.trans (ExpGB.psJet_zero_of _ (const_ad C a)))
  have hι : homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S) ≫
      lift (jpt y C.d C.x 0 (0 : Fin 2)) (jpt y C.d C.x 0 (1 : Fin 2)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G) := by
    rw [jet_point_zero_eq_one C, jet_point_zero_eq_one C, comp_lift]
    exact congrArg₂ (fun p q => lift p q) (comp_one' _) (comp_one' _)
  have h1 := val_corr hJ hc (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left)
  rw [val_mul hJ, val_pull hJ, val_scale' _ _ _ _ _ z J hJ, hu1,
    show unitΓ (1 : (Jet S (Fin 2 × Fin C.d) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
    _root_.one_mul] at h1
  have hpe : val (pe y C.d C.x C.e 0 ![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J =
      val (pe y C.d C.x C.e 0 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)])
        (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J := by
    have hm : (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left =
        (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left := by
      rw [jet_zero_hom_ext (jetSubstP 0 _) (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)]
    unfold pe
    rw [hm]
  rw [hpe, mul_eq_right] at h1
  rw [Category.assoc, ← Over.comp_left, hι] at h1
  exact h1
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
