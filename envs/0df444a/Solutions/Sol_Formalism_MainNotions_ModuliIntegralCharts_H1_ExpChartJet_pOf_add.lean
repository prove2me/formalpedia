-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.pOf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:23.287045+00:00
-- url     : https://prove2.me/submissions/212ecc70-e2f1-468f-bc85-b20a889ed339

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_fin_one_pair_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_lin_F
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
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
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (g g' : Fin 1 × Fin C.d → S) : pOf C (g + g') = pOf C g * pOf C g' := by
  have hc : ∀ i : Fin 2, (tp2 C g g').comp (jetCopy C.d (0 + 1) i) =
      tp (fun q : Fin 1 × Fin C.d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) i q.2) := by
    intro i
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, tp2, tp_mk, tp_mk]
  have h0 : tp (fun q : Fin 1 × Fin C.d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) 0 q.2) = tp g := by
    congr 1
    funext q
    simp only [Matrix.cons_val_zero, fin_one_pair_eq]
  have h1 : tp (fun q : Fin 1 × Fin C.d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) 1 q.2) = tp g' := by
    congr 1
    funext q
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, fin_one_pair_eq]
  have hF : (tp2 C g g').comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2)) = tp (g + g') := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2) (fun p => C.B.G.const p.2),
      tp2, tp_psJet, tp_mk, C.B.G.const, TrivSqZeroExt.inl_zero, zero_add, lin_F]
    simp only [Pi.add_apply, fin_one_pair_eq]
  have hl : homAt y.x (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2)) ≫ C.x 1 =
      (homAt y.x (jetCopy C.d (0 + 1) (0 : Fin 2)) ≫ C.x 1) * (homAt y.x (jetCopy C.d (0 + 1) (1 : Fin 2)) ≫ C.x 1) :=
    C.chart.law 1
  have e := congrArg (fun f => homAt y.x (tp2 C g g') ≫ f) hl
  simp only [MonObj.comp_mul, ← Category.assoc, GermD.homAt_comp, hc, hF, h0, h1] at e
  exact e
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
