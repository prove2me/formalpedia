-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.sy_inv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:34.423071+00:00
-- url     : https://prove2.me/submissions/6d29f1b7-0f59-437b-9df3-21ca861458f6

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_psJet_ev_swap
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_sy_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
section Alg
variable {S : Type} [CommRing S] (d : ℕ)
private theorem degree_eq_sum_lemma_2 {τ : Type} (e : τ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree, Finsupp.sum]
private theorem degree_add_lemma_3 {τ : Type} (a b : τ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add Finsupp.degree a b
  | (rw [degree_eq_sum_lemma_2, degree_eq_sum_lemma_2, degree_eq_sum_lemma_2]
     exact Finsupp.sum_add_index' (h := fun _ k => k) (fun _ => rfl) (fun _ _ _ => rfl))
private theorem le_degree_lemma_4 {τ : Type} (e : τ →₀ ℕ) (i : τ) : e i ≤ e.degree := by
  by_cases h : e i = 0
  · rw [h]; exact Nat.zero_le _
  · rw [degree_eq_sum_lemma_2]
    exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.2 h)
private theorem coeff_eq_zero_of_mem_orig_pow_lemma_5 {τ : Type} (n : ℕ) (x : MvPolynomial τ S)
    (hx : x ∈ orig S τ ^ n) (e : τ →₀ ℕ) (he : e.degree < n) : coeff e x = 0 := by
  classical
  induction n generalizing x e with
  | zero => exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ] at hx
    revert e
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · intro e he
      have hle : orig S τ ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial τ S →+* S) :=
        Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp)
      have hb0 : coeff 0 b = 0 := by
        have h0 : MvPolynomial.constantCoeff b = 0 := RingHom.mem_ker.1 (hle hb)
        exact h0
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun u hu => ?_
      have hu' := Finset.HasAntidiagonal.mem_antidiagonal.1 hu
      by_cases h1 : u.1.degree < n
      · rw [ih a ha u.1 h1, zero_mul]
      · have hd : u.1.degree + u.2.degree = e.degree := by rw [← hu', degree_add_lemma_3]
        have h2 : u.2 = 0 := by
          ext i
          have := le_degree_lemma_4 u.2 i
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        rw [h2, hb0, mul_zero]
    · intro e he
      rw [coeff_add, hy e he, hz e he, add_zero]
private theorem mem_degLE_lemma_6 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (e : τ →₀ ℕ) :
    e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    rw [degree_eq_sum_lemma_2]
    exact h
  · intro h
    refine ⟨⟨fun i => ⟨e i, by have := le_degree_lemma_4 e i; omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [degree_eq_sum_lemma_2] at h
      exact h
private theorem coeff_psTrunc_lemma_7 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (e : τ →₀ ℕ) :
    coeff e (psTrunc m f) = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  rw [psTrunc, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_degLE_lemma_6]
private theorem mem_orig_pow_of_coeff_lemma_8 {τ : Type} (n : ℕ) (p : MvPolynomial τ S)
    (h : ∀ e : τ →₀ ℕ, e.degree < n → coeff e p = 0) : p ∈ orig S τ ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun e he => ?_
  have hn : n ≤ e.degree := by
    by_contra hlt
    exact (MvPolynomial.mem_support_iff.1 he) (h e (not_le.1 hlt))
  refine Ideal.pow_le_pow_right hn ?_
  rw [MvPolynomial.monomial_eq, degree_eq_sum_lemma_2, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.mul_mem_left _ _ (Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow ?_ _)
  exact Ideal.subset_span ⟨i, rfl⟩
private theorem psJet_eq_mk_lemma_9 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (p : MvPolynomial τ S)
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ m → coeff e p = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  rw [psJet, Ideal.Quotient.eq]
  refine mem_orig_pow_of_coeff_lemma_8 (m + 1) _ fun e he => ?_
  have he' : e.degree ≤ m := Nat.lt_succ_iff.1 he
  rw [coeff_sub, coeff_psTrunc_lemma_7, if_pos he', h e he', sub_self]
private theorem psJet_mul_lemma_10 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f g : MvPowerSeries τ S) : psJet m (f * g) = psJet m f * psJet m g := by
  show psJet m (f * g) = Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m f) *
    Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m g)
  rw [← map_mul]
  refine psJet_eq_mk_lemma_9 m _ _ fun e he => ?_
  rw [coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hd : x.1.degree + x.2.degree = e.degree := by rw [← hx', degree_add_lemma_3]
  rw [coeff_psTrunc_lemma_7, coeff_psTrunc_lemma_7, if_pos (by omega), if_pos (by omega)]
private theorem psJet_one_lemma_11 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psJet m (1 : MvPowerSeries τ S) = 1 := by
  rw [show (1 : Jet S τ m) = Ideal.Quotient.mk (orig S τ ^ (m + 1)) 1 from (map_one _).symm]
  refine psJet_eq_mk_lemma_9 m 1 1 fun e _ => ?_
  rw [MvPolynomial.coeff_one, MvPowerSeries.coeff_one]
  by_cases h : e = 0
  · subst h; simp
  · simp [h, Ne.symm h]
private theorem eq_of_psJet_lemma_12 {τ : Type} [Fintype τ] [DecidableEq τ] (f g : MvPowerSeries τ S)
    (h : ∀ m, psJet m f = psJet m g) : f = g := by
  ext e
  have h1 := h e.degree
  rw [psJet, psJet, Ideal.Quotient.eq] at h1
  have h2 := coeff_eq_zero_of_mem_orig_pow_lemma_5 _ _ h1 e (Nat.lt_succ_self _)
  rw [coeff_sub, coeff_psTrunc_lemma_7, coeff_psTrunc_lemma_7, if_pos le_rfl, if_pos le_rfl, sub_eq_zero] at h2
  exact h2
end Alg
section Axes
variable {S : Type} [CommRing S] (d : ℕ)
end Axes
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
end Frame
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
theorem _root_.solution (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) :
    sy * ev (n := 2) ![pt S d 1, pt S d 0] sy = 1 := by
  refine eq_of_psJet_lemma_12 _ _ fun m => ?_
  rw [psJet_mul_lemma_10, psJet_ev_swap, sy_unit t x0 d x hL hfr m, psJet_one_lemma_11]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
