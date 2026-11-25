-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.xExp_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:24.790164+00:00
-- url     : https://prove2.me/submissions/b35eca81-5cfc-4ccb-8485-0c9b529230e8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_fin_one_pair_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_pOf_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_eps_pOf
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_tan_j__f39747463092
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_jetTan_eq_tp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp


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
variable (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (hφ : IsExpOf C.B.G.F C.uvec φ) (ℓ : Lt1 Dw) : IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ xExp y C φ 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2) := by
  have hv : ∀ j : Fin (dL Dw), homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ xExp y C φ 1 =
      homAt y.x (tp fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) ≫
        C.x 1 := by
    intro j
    show homAt y.x _ ≫ (homAt y.x (jφ φ (0 + 1)) ≫ C.x 1) = _
    rw [← Category.assoc, GermD.homAt_comp, tan_jφ C φ hφ j]
  obtain ⟨u, hu, hprod⟩ := C.chart.tan ℓ
  have hu' : u = fun i => pOf C (C.uvec ℓ i • fun q : Fin 1 × Fin C.d => if q = ((0 : Fin 1), i) then (1 : S) else 0) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hu i]
    dsimp only
    rw [jetTan_eq_tp, eps_pOf]
  have hq : ∀ (q : Fin 1 × Fin C.d) (i : Fin C.d), (q = ((0 : Fin 1), i)) = (i = q.2) := fun q i =>
    propext ⟨fun h => by rw [h], fun h => by rw [h, fin_one_pair_eq]⟩
  have hs1 : (∑ i, C.uvec ℓ i • fun q : Fin 1 × Fin C.d => if q = ((0 : Fin 1), i) then (1 : S) else 0) =
      fun q => C.uvec ℓ q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hq, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have hy : (pOf C fun q => C.uvec ℓ q.2).left = y.u ℓ.1 ℓ.2 := by
    rw [← hs1, pOf_sum, ← hprod, hu']
  have hs2 : (∑ j : Fin (dL Dw), (if j = ltIdx Dw ℓ then (1 : S) else 0) •
      fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) =
      fun q => C.uvec ℓ q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [_root_.one_mul]
    exact hφ.lin ℓ q.2
  refine ⟨fun j => pOf C ((if j = ltIdx Dw ℓ then (1 : S) else 0) •
    fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)), fun j => ?_, ?_⟩
  · dsimp only
    rw [hv j, eps_pOf]
  · rw [← pOf_sum, hs2, hy]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
