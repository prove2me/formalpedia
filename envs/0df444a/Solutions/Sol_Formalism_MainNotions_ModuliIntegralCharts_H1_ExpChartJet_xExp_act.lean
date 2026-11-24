-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.xExp_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:23.249358+00:00
-- url     : https://prove2.me/submissions/505c4d21-2624-4bda-a144-67f251b02249

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_const_coeff_coe_zero
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstP_eq_jetSubstPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_actS_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (hφ : IsExpOf C.B.G.F C.uvec φ) (hA : ExpActOf C φ) (m : ℕ) (a : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a)) ≫ xExp y C φ m := by
  have hP : ∀ q, MvPolynomial.constantCoeff (actP (Dw := Dw) (S := S) c a q) = 0 := fun q => by simp [actP]
  have hA' : (jφ φ m).comp (jetSubstPS (m := m) (fun p : Fin 1 × Fin C.d => C.B.A.act a p.2)) =
      (jetSubstP m (actP (Dw := Dw) (S := S) c a)).comp (jφ φ m) := by
    rw [jetSubstP_eq_jetSubstPS m _ hP]
    apply jet_hom_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jφ, jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => C.B.A.act a p.2) (fun q => C.B.A.const a q.2),
      jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2), jetSubstPS_psJet m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2),
      jetSubstPS_psJet m (fun q : Fin 1 × Fin (dL Dw) => (actP (Dw := Dw) (S := S) c a q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S))
        (fun q => const_coeff_coe_zero _ (hP q)), hA a p.2, actS_eq]
  have hC : C.x m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstPS (m := m) (fun p : Fin 1 × Fin C.d => C.B.A.act a p.2)) ≫ C.x m :=
    C.chart.act m a
  rw [xExp, Category.assoc, hC, ← Category.assoc, GermD.homAt_comp, hA', ← GermD.homAt_comp, Category.assoc]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
