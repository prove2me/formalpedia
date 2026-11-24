-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.jetSubstPS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:13.791798+00:00
-- url     : https://prove2.me/submissions/ed4fab26-b35f-48f7-8f1d-7d25a1d51991

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
section Jets
variable {R : Type} [CommRing R]
private lemma cc_psTrunc_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  rw [map_sum, Finset.sum_eq_single 0]
  · rw [MvPolynomial.constantCoeff_monomial, if_pos rfl]
    first | rfl | simp
  · intro e _ he
    rw [MvPolynomial.constantCoeff_monomial, if_neg he]
  · intro h0
    exfalso
    apply h0
    unfold degLE
    rw [Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨fun _ => 0, Finset.mem_univ _, ?_⟩, by simp⟩
    ext i
    simp
end Jets
section Chart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
end Chart
section Tan
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y)
variable (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
end Tan
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
end Main
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0) :
    (jetSubstPS (m := m) g) = jetMap (fun i => psTrunc m (g i)) (fun i => psTrunc_mem_orig m (g i) (hg i)) := by
  have e : ∀ i, psTrunc m (g i) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (g i))) = psTrunc m (g i) :=
    fun i => by rw [cc_psTrunc_lemma, hg i, map_zero, sub_zero]
  unfold jetSubstPS jetMap
  first
  | (simp only [e]; done)
  | (congr 1; simp only [e]; done)
  | (congr; funext i; exact e i)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
