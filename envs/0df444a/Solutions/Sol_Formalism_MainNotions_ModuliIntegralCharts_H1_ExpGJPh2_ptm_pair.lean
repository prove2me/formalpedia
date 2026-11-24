-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2.ptm_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:56.133602+00:00
-- url     : https://prove2.me/submissions/101745cf-08f6-49f6-ba05-07e756e4f075

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_subst
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const__a_6a1787d574a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
set_option maxHeartbeats 1000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) (u0 u1 u2 : 𝓞 E) (a b : Fin 3) :
    ptm C (P3 C φ u0 u1 u2) m ≫ homAt y.x (jetSubstP m (σ2 C a b)) =
      ptm C ![φa c φ (![u0, u1, u2] a), φa c φ (![u0, u1, u2] b)] m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P3 C φ u0 u1 u2 i j) = 0 :=
    fun i j => ExpGG.const_φa c φ hφ _ j
  have hσ : ∀ k, MvPolynomial.constantCoeff (σ2 C a b k) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [σ2]
  rw [ptm_subst C _ hP m (σ2 C a b) hσ]
  have hs : MvPowerSeries.HasSubst (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hP p.1 p.2]; exact IsNilpotent.zero)
  congr 1
  funext i j
  fin_cases i <;> simp [σ2, MvPolynomial.coe_X, MvPowerSeries.subst_X hs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
