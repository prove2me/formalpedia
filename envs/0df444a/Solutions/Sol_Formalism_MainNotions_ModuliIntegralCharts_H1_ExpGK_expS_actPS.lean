-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK.expS_actPS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:45:38.322356+00:00
-- url     : https://prove2.me/submissions/ca7e8f64-1a15-4f2a-abc6-0bedbd954854

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_const_compL


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
theorem _root_.solution {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d) S)
    (hg : MvPowerSeries.constantCoeff g = 0) (k : 𝓞 E) :
    MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (Germ.FB.expS S (-(compL φ g))) =
      Germ.FB.expS S (-(compL (φa c φ k) g)) := by
  have hb : MvPowerSeries.HasSubst (actPS (Dw := Dw) (S := S) c k) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by simp [actPS]
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hφ p.2
  have h0 : MvPowerSeries.constantCoeff (-(compL φ g)) = 0 := by
    rw [map_neg, ExpGB.const_compL φ hφ g, hg, neg_zero]
  have hcomp : MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (-(compL φ g)) =
      -(compL (φa c φ k) g) := by
    rw [← MvPowerSeries.coe_substAlgHom hb, map_neg, MvPowerSeries.coe_substAlgHom hb]
    unfold compL φa
    rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  unfold Germ.FB.expS PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h0).const hb]
  simp only [hcomp]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
