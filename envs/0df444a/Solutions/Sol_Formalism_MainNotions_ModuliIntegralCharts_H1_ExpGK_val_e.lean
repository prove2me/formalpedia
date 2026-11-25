-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK.val_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:48.654432+00:00
-- url     : https://prove2.me/submissions/4bcafb98-594c-463d-a136-5882bad39239

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_val_eAt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (u m)) *
        (val C.wP ((ptm C ![φ] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φ, φa c φ H.w0] m).left z J) := by
  have hX : actP (Dw := Dw) (S := S) c 1 = fun p => MvPolynomial.X p := by
    funext p
    simp [actP]
  have hid : jetSubstP m (actP (Dw := Dw) (S := S) c 1) = AlgHom.id S _ := by
    rw [hX]
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [jetSubstP, jetMap, liftJet, Ideal.Quotient.lift_mk] <;> rfl
  have hP : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  have hφ1 : φa c φ 1 = φ := by
    funext j
    simp only [φa, hP]
    exact congrFun MvPowerSeries.subst_self (φ j)
  have hu : Units.map (AlgHom.id S (Jet S (Fin 1 × Fin (dL Dw)) m)).toMonoidHom (u m) = u m :=
    Units.ext rfl
  have h1 := val_eAt C φ hφ hact τ u hτc m 1 z J hJ
  rw [hφ1, _root_.mul_one] at h1
  unfold eAt at h1
  rw [val_pull, hid, homAt_id, Over.id_left, Category.comp_id, hu] at h1
  exact h1
  exact hJ
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
