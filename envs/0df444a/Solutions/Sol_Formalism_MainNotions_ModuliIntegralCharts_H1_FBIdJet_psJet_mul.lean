-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:17.295465+00:00
-- url     : https://prove2.me/submissions/4b5515b7-f000-488d-b69f-9b2d983af1c9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
private lemma mem_orig_pow_lemma_6 {ι : Type} (m : ℕ) (Q : MvPolynomial ι R)
    (hQ : ∀ e : ι →₀ ℕ, e.degree < m + 1 → MvPolynomial.coeff e Q = 0) :
    Q ∈ orig R ι ^ (m + 1) := by
  rw [Q.as_sum]
  refine Ideal.sum_mem _ fun e he => ?_
  have hd : m + 1 ≤ e.degree := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 he) (hQ e (by omega))
  rw [MvPolynomial.monomial_eq]
  refine Ideal.mul_mem_left _ _ ?_
  refine Ideal.pow_le_pow_right hd ?_
  have hX : ∀ i, (MvPolynomial.X i : MvPolynomial ι R) ∈ orig R ι := fun i => by
    first
    | exact Ideal.subset_span ⟨i, rfl⟩
    | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩)
  have h1 : (∏ i ∈ e.support, (MvPolynomial.X i : MvPolynomial ι R) ^ e i) ∈
      ∏ i ∈ e.support, orig R ι ^ e i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _
  rw [Finset.prod_pow_eq_pow_sum] at h1
  first
  | exact h1
  | (unfold Finsupp.prod; simpa [Finsupp.degree] using h1)
private lemma coe_sub_lemma_7 {ι : Type} (x y : MvPolynomial ι R) :
    ((x - y : MvPolynomial ι R) : MvPowerSeries ι R) = (x : MvPowerSeries ι R) - y := by
  rw [eq_sub_iff_add_eq, ← MvPolynomial.coe_add, sub_add_cancel]
private lemma low_mul_lemma {τ : Type} {F G : MvPowerSeries τ R} {p q : ℕ}
    (hF : ∀ e : τ →₀ ℕ, e.degree < p → MvPowerSeries.coeff e F = 0)
    (hG : ∀ e : τ →₀ ℕ, e.degree < q → MvPowerSeries.coeff e G = 0) :
    ∀ e : τ →₀ ℕ, e.degree < p + q → MvPowerSeries.coeff e (F * G) = 0 := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  replace hx : x.1 + x.2 = e := by
    first
    | exact Finset.mem_antidiagonal.1 hx
    | simpa using hx
    | exact Finsupp.mem_antidiagonal.1 hx
  have hd : x.1.degree + x.2.degree = e.degree := by
    rw [← hx]
    first
    | exact (map_add Finsupp.degree x.1 x.2).symm
    | exact (Finsupp.degree_add x.1 x.2).symm
    | simp [Finsupp.degree, Finsupp.sum_add_index']
    | (simp only [Finsupp.degree_eq_weight_one, map_add])
  by_cases h1 : x.1.degree < p
  · rw [hF _ h1, zero_mul]
  · rw [hG _ (by omega), mul_zero]
private lemma low_trunc_lemma_5 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (F : MvPowerSeries ι R) :
    ∀ e : ι →₀ ℕ, e.degree < m + 1 →
      MvPowerSeries.coeff e (F - (psTrunc m F : MvPowerSeries ι R)) = 0 := by
  intro e he
  first
  | (rw [map_sub, MvPolynomial.coeff_coe, psTrunc_eq, MvPowerSeries.coeff_truncTotal,
      sub_self] <;> exact he)
  | simp [psTrunc_eq, MvPowerSeries.coeff_truncTotal, he]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f g : MvPowerSeries ι R) :
    psJet m (f * g) = psJet m f * psJet m g := by
  unfold psJet
  rw [← map_mul, Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_6
  intro e he
  have h1 := low_mul_lemma (G := g) (q := 0) (low_trunc_lemma_5 m f)
    (fun d hd => absurd hd (Nat.not_lt_zero _)) e (by omega)
  have h2 := low_mul_lemma (F := (psTrunc m f : MvPowerSeries ι R)) (p := 0)
    (fun d hd => absurd hd (Nat.not_lt_zero _)) (low_trunc_lemma_5 m g) e (by omega)
  have h3 := low_trunc_lemma_5 m (f * g) e he
  have hcoe : MvPolynomial.coeff e (psTrunc m (f * g) - psTrunc m f * psTrunc m g) =
      MvPowerSeries.coeff e ((f - (psTrunc m f : MvPowerSeries ι R)) * g +
        (psTrunc m f : MvPowerSeries ι R) * (g - (psTrunc m g : MvPowerSeries ι R)) -
        (f * g - (psTrunc m (f * g) : MvPowerSeries ι R))) := by
    rw [← MvPolynomial.coeff_coe, coe_sub_lemma_7, MvPolynomial.coe_mul]
    first
    | (congr 1; ring)
    | exact congrArg _ (by ring)
  rw [hcoe, map_sub, map_add, h1, h2, h3, add_zero, sub_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
