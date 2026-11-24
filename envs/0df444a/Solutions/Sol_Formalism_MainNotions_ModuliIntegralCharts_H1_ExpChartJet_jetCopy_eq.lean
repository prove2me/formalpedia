-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.jetCopy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:12.517589+00:00
-- url     : https://prove2.me/submissions/dbe8e79e-e4a2-4ccf-a589-30b4b9f07115

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
private lemma mono_mem_lemma_2 {κ : Type} (m : ℕ) (e : κ →₀ ℕ) (c : R) (he : m + 1 ≤ e.sum fun _ k => k) :
    MvPolynomial.monomial e c ∈ orig R κ ^ (m + 1) := by
  have hX : ∀ j, (MvPolynomial.X j : MvPolynomial κ R) ∈ orig R κ := fun j => by
    unfold orig
    exact Ideal.subset_span ⟨j, rfl⟩
  rw [MvPolynomial.monomial_eq]
  apply Ideal.mul_mem_left
  refine Ideal.pow_le_pow_right he ?_
  rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (hX j) _
private lemma mem_of_coeff_lemma_3 {κ : Type} (m : ℕ) (Q : MvPolynomial κ R)
    (h : ∀ e : κ →₀ ℕ, (e.sum fun _ k => k) ≤ m → MvPolynomial.coeff e Q = 0) : Q ∈ orig R κ ^ (m + 1) := by
  rw [MvPolynomial.as_sum Q]
  refine Ideal.sum_mem _ fun e he => mono_mem_lemma_2 m e _ ?_
  by_contra hlt
  exact (MvPolynomial.mem_support_iff.mp he) (h e (by omega))
private lemma mem_degLE_lemma_5 {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ (e.sum fun _ k => k) ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩
    · have hi : e i ≤ e.sum fun _ k => k := by
        by_cases hs : i ∈ e.support
        · exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) hs
        · have h0 : e i = 0 := by simpa using hs
          omega
      omega
    · ext i
      simp
private lemma coeff_psTrunc_lemma_4 {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R)
    (e : κ →₀ ℕ) :
    MvPolynomial.coeff e (psTrunc m f) = if e ∈ degLE m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i = jetSubstPS (m := m)
      (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  unfold jetCopy jetSubstPS jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  apply mem_of_coeff_lemma_3
  intro e he
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_4, if_pos ((mem_degLE_lemma_5 m e).mpr he),
    cc_psTrunc_lemma, MvPowerSeries.constantCoeff_X, map_zero, MvPolynomial.coeff_zero, sub_zero,
    ← MvPolynomial.coe_X, MvPolynomial.coeff_coe, sub_self]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
