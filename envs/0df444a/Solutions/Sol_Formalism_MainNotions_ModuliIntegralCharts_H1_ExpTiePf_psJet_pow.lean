-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf.psJet_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:44.643369+00:00
-- url     : https://prove2.me/submissions/f857a0f1-5320-4bbd-9024-934d0b9a4651

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
private lemma mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ (e.sum fun _ k => k) ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_image]
    refine ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hi : e i ≤ e.sum fun _ k => k := by
        by_cases hi0 : e i = 0
        · omega
        · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
            (Finsupp.mem_support_iff.2 hi0)
      omega
    · ext i
      simp
private lemma coeff_psTrunc_lemma_2 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (f : MvPowerSeries κ R) (e : κ →₀ ℕ) (he : (e.sum fun _ k => k) ≤ m) :
    MvPolynomial.coeff e (psTrunc m f) = MvPowerSeries.coeff e f := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single e]
  · simp [MvPolynomial.coeff_monomial]
  · intro b _ hb
    simp [MvPolynomial.coeff_monomial, hb]
  · intro h
    exact absurd ((mem_degLE_lemma m e).2 he) h
private lemma mem_orig_pow_lemma_3 {R κ : Type} [CommRing R] (m : ℕ) (p : MvPolynomial κ R)
    (hp : ∀ e : κ →₀ ℕ, (e.sum fun _ k => k) ≤ m → MvPolynomial.coeff e p = 0) :
    p ∈ orig R κ ^ (m + 1) := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun e _ => ?_
  by_cases he : (e.sum fun _ k => k) ≤ m
  · rw [hp e he, map_zero]
    exact Ideal.zero_mem _
  · have h1 : MvPolynomial.monomial e (MvPolynomial.coeff e p) ∈
        orig R κ ^ (e.sum fun _ k => k) := by
      rw [MvPolynomial.monomial_eq]
      refine Ideal.mul_mem_left _ _ ?_
      rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
    exact Ideal.pow_le_pow_right (by omega) h1
private lemma psJet_mul_lemma_4 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (f g : MvPowerSeries κ R) : psJet m (f * g) = psJet m f * psJet m g := by
  unfold psJet
  rw [← map_mul, Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_3
  intro e he
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_mul, coeff_psTrunc_lemma_2 m _ e he,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpe : p.1 + p.2 = e := by simpa using hp
  have hd : (p.1.sum fun _ k => k) + (p.2.sum fun _ k => k) = e.sum fun _ k => k := by
    rw [← hpe, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [coeff_psTrunc_lemma_2 m f p.1 (by omega), coeff_psTrunc_lemma_2 m g p.2 (by omega)]
private lemma psJet_one_lemma_5 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) :
    psJet m (1 : MvPowerSeries κ R) = 1 := by
  unfold psJet
  rw [← map_one (Ideal.Quotient.mk (orig R κ ^ (m + 1))), Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_3
  intro e he
  rw [MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2 m _ e he, MvPowerSeries.coeff_one,
    MvPolynomial.coeff_one]
  by_cases h0 : e = 0
  · subst h0
    simp
  · simp [h0, Ne.symm h0]
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
end Main
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries ExpTieAlg ExpTieGerm ExpTiePf
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
theorem _root_.solution {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R) (k : ℕ) :
    psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact psJet_one_lemma_5 m
  | succ k ih =>
    rw [pow_succ, psJet_mul_lemma_4, ih]
    exact (pow_succ _ _).symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
