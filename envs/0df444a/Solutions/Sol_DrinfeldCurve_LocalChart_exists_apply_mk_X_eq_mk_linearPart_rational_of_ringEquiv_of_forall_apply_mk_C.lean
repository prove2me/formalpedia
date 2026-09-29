-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/282aa925-a664-5cf5-ac22-2db57b397877

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Theorems.Thm_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C

set_option autoImplicit false

open IsLocalRing

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "LocalChart.drinfeldForm mk mk_surjective x y LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero"
namespace LocalChart
p2m_export "DrinfeldCurve.LocalChart" "drinfeldForm coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero"
namespace LinearPartAux
p2m_open "DrinfeldCurve.LocalChart DrinfeldCurve"

open MvPowerSeries

theorem eq_zero_of_deg_lt_one (n : Fin 2 →₀ ℕ) (h : n 0 + n 1 < 1) : n = 0 := by
  ext i; fin_cases i <;> simp <;> omega

theorem eq_of_deg_lt_two (n : Fin 2 →₀ ℕ) (h : n 0 + n 1 < 2) :
    n = 0 ∨ n = Finsupp.single 0 1 ∨ n = Finsupp.single 1 1 := by
  rcases Nat.lt_or_ge (n 0 + n 1) 1 with h1 | h1
  · exact Or.inl (eq_zero_of_deg_lt_one n h1)
  · have : n 0 + n 1 = 1 := by omega
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · right; right; ext i; fin_cases i <;> simp <;> omega
    · right; left; ext i; fin_cases i <;> simp <;> omega

theorem prod_sub_natCast (q : ℕ) [hq : Fact q.Prime] (K : Type*) [CommRing K] [CharP K q] (t : K) :
    ∏ a : Fin q, (t - ((a : ℕ) : K)) = t ^ q - t := by
  classical
  have h1 : (1 : ℕ) < q := hq.out.one_lt
  have hmonic : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)
  have hroots : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod q)
    rwa [ZMod.card] at this
  have hcard : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).roots.card =
      (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ h1]
    simp [ZMod.card]
  have hpoly := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots] at hpoly
  have hpoly' : ∏ a : ZMod q, (Polynomial.X - Polynomial.C a) = (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)) := by
    rw [Finset.prod_eq_multiset_prod]; exact hpoly
  let φ : ZMod q →+* K := ZMod.castHom (dvd_refl q) K
  have h2 := congrArg (Polynomial.eval₂RingHom φ t) hpoly'
  simp only [map_prod, map_sub, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
  rw [← h2]
  refine Fintype.prod_bijective (fun a : Fin q => ((a : ℕ) : ZMod q)) ?_ _ _ (fun a => ?_)
  · refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [ZMod.card]⟩
    intro a b hab
    have := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
    exact Fin.ext this
  · simp [φ, map_natCast]

theorem exists_natCast_eq_of_pow_eq (q : ℕ) [hq : Fact q.Prime] (K : Type*) [Field K] [CharP K q]
    (μ : K) (hμ : μ ^ q = μ) : ∃ n : ℕ, n < q ∧ ((n : ℕ) : K) = μ := by
  classical
  have h := prod_sub_natCast q K μ
  rw [hμ, sub_self] at h
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨a, a.isLt, (sub_eq_zero.mp ha).symm⟩

theorem mul_pow_sub_mul_pow_mem {A : Type*} [CommRing A] (I : Ideal A) (a a' b b' : A)
    (ha' : a' ∈ I) (hb : b ∈ I) (hb' : b' ∈ I)
    (h1 : a - a' ∈ I ^ 2) (h2 : b - b' ∈ I ^ 2) (n : ℕ) (hn : 1 ≤ n) :
    a * b ^ n - a' * b' ^ n ∈ I ^ (n + 2) := by
  have e : a * b ^ n - a' * b' ^ n = (a - a') * b ^ n + a' * (b ^ n - b' ^ n) := by ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · have := Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hb n)
    rwa [← pow_add, add_comm] at this
  · have hs : (∑ i ∈ Finset.range n, b ^ i * b' ^ (n - 1 - i)) ∈ I ^ (n - 1) := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hb i) (Ideal.pow_mem_pow hb' (n - 1 - i))
      rwa [← pow_add, show i + (n - 1 - i) = n - 1 by omega] at this
    rw [← geom_sum₂_mul, ← mul_assoc]
    have hI : I ^ (n + 2) = I * I ^ (n - 1) * I ^ 2 := by
      rw [← pow_succ', show n - 1 + 1 = n by omega, ← pow_add]
    rw [hI]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_mul ha' hs) h2

section chart

variable {W : Type} [CommRing W]

theorem coeff_drinfeldForm_eq_zero_of_lt (q : ℕ) [Fact q.Prime] (n : Fin 2 →₀ ℕ) (h : n 0 + n 1 < q + 1) :
    coeff n (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
  classical
  have e1 : (X 0 : MvPowerSeries (Fin 2) W) * X 1 ^ q = monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  have e2 : (X 0 : MvPowerSeries (Fin 2) W) ^ q * X 1 = monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  unfold DrinfeldCurve.LocalChart.drinfeldForm
  rw [e1, e2, map_sub, coeff_monomial, coeff_monomial, if_neg, if_neg, sub_zero]
  · intro hn; subst hn; simp at h
  · intro hn; subst hn; simp at h

theorem drinfeldForm_mem_pow (q : ℕ) [Fact q.Prime] :
    DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 1) :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 1) _).mpr
    (fun n hn => coeff_drinfeldForm_eq_zero_of_lt q n hn)

theorem constantCoeff_eq_zero_of_sub_drinfeldForm_mem (q : ℕ) [Fact q.Prime] (f : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2)) :
    constantCoeff f = 0 := by
  have h1 := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 2) _).mp hf 0 (by simp)
  have h2 := coeff_drinfeldForm_eq_zero_of_lt (W := W) q 0 (by simp)
  rw [map_sub, h2, sub_zero, coeff_zero_eq_constantCoeff_apply] at h1
  exact h1

theorem mem_span_X_iff_constantCoeff (g : MvPowerSeries (Fin 2) W) :
    g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ↔ constantCoeff g = 0 := by
  have := MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 1 g
  rw [pow_one] at this
  rw [this]
  constructor
  · intro h; rw [← coeff_zero_eq_constantCoeff_apply]; exact h 0 (by simp)
  · intro h n hn; rw [eq_zero_of_deg_lt_one n hn, coeff_zero_eq_constantCoeff_apply]; exact h

variable [IsLocalRing W]

theorem constantCoeff_mem_maximalIdeal_of_not_isUnit_mk (J : Ideal (MvPowerSeries (Fin 2) W))
    (g : MvPowerSeries (Fin 2) W) (h : ¬ IsUnit (Ideal.Quotient.mk J g)) :
    constantCoeff g ∈ maximalIdeal W := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact h ((isUnit_iff_constantCoeff.mpr hu).map _)

theorem not_isUnit_mk_of_constantCoeff_mem (π : W) (hπ : π ∈ maximalIdeal W) (f u v : MvPowerSeries (Fin 2) W)
    (hf : constantCoeff f = 0) (g : MvPowerSeries (Fin 2) W) (hg : constantCoeff g ∈ maximalIdeal W) :
    ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) g) := by
  set φ : MvPowerSeries (Fin 2) W →+* ResidueField W := (residue W).comp constantCoeff with hφ
  have hker : ∀ a ∈ Ideal.span {C π * v - f * u}, φ a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [hφ, RingHom.coe_comp, Function.comp_apply, map_mul, map_sub, constantCoeff_C, hf, zero_mul,
      sub_zero]
    rw [(residue_eq_zero_iff π).mpr hπ]; simp
  intro hunit
  have h1 := hunit.map (Ideal.Quotient.lift _ φ hker)
  rw [Ideal.Quotient.lift_mk] at h1
  simp only [hφ, RingHom.coe_comp, Function.comp_apply] at h1
  rw [(residue_eq_zero_iff _).mpr hg] at h1
  exact not_isUnit_zero h1

theorem exists_rep_constantCoeff_eq_zero (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (f u v : MvPowerSeries (Fin 2) W)
    (hv : IsUnit v) (hf : constantCoeff f = 0)
    (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {C π * v - f * u}) (hs : ¬ IsUnit s) :
    ∃ g : MvPowerSeries (Fin 2) W, constantCoeff g = 0 ∧ Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) g = s := by
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective s
  have hc := constantCoeff_mem_maximalIdeal_of_not_isUnit_mk _ g' hs
  rw [hπ] at hc
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hc
  obtain ⟨v0, hv0⟩ := isUnit_iff_constantCoeff.mp hv
  refine ⟨g' - C (w * ↑v0⁻¹) * (C π * v - f * u), ?_, ?_⟩
  · simp only [map_sub, map_mul, constantCoeff_C, hf, zero_mul, sub_zero, ← hv0, ← hw]
    have hvv : ((↑v0⁻¹ : W)) * ↑v0 = 1 := Units.inv_mul v0
    linear_combination (-(w * π)) * hvv
  · rw [Ideal.Quotient.eq]
    simp only [sub_sub_cancel_left, neg_mem_iff]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

omit [IsLocalRing W] in

theorem exists_rep_mem_pow_of_mem_map_pow (J : Ideal (MvPowerSeries (Fin 2) W)) (e : ℕ)
    (s : MvPowerSeries (Fin 2) W ⧸ J)
    (hs : s ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk J)) ^ e) :
    ∃ g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e, Ideal.Quotient.mk J g = s := by
  rw [← Ideal.map_pow] at hs
  exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hs

omit [IsLocalRing W] in
theorem mk_mem_map_pow_of_mem_pow (J : Ideal (MvPowerSeries (Fin 2) W)) (e : ℕ)
    (g : MvPowerSeries (Fin 2) W) (hg : g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e) :
    Ideal.Quotient.mk J g ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk J)) ^ e := by
  rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hg

omit [IsLocalRing W] in

theorem coeff_mem_span_of_mk_mem_pow_succ [IsDomain W] (π : W) (hπ : π ≠ 0) (f u v : MvPowerSeries (Fin 2) W)
    (hv : IsUnit v) (hf : constantCoeff f = 0) (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ e)
    (hmk : Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) g ∈
      ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}))) ^ (e + 1))
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 = e) :
    coeff n g ∈ Ideal.span {π} := by
  obtain ⟨g₁, hg₁, hg₁eq⟩ := exists_rep_mem_pow_of_mem_map_pow _ (e + 1) _ hmk
  have hdiff : g - g₁ ∈ Ideal.span {C π * v - f * u} := by
    rw [← Ideal.Quotient.eq, hg₁eq]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hdiff
  have hrel : g = g₁ + (C π * v - f * u) * r := by rw [mul_comm, hr]; ring
  have hf0 : coeff (0 : Fin 2 →₀ ℕ) f = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact hf
  exact DrinfeldCurve.LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero W π hπ f u v hv hf0 e g g₁ r
    ((MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g).mp hg)
    ((MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (e + 1) g₁).mp hg₁) hrel n hn

end chart

section linforms

variable {W : Type} [CommRing W]

theorem coeff_single_X (j k : Fin 2) :
    coeff (Finsupp.single j 1) (X k : MvPowerSeries (Fin 2) W) = if j = k then 1 else 0 := by
  classical
  rw [coeff_X]
  by_cases h : j = k
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro hh
    exact h (Finsupp.single_left_injective one_ne_zero hh)

theorem coeff_single_lin (a₀ a₁ : W) (j : Fin 2) :
    coeff (Finsupp.single j 1) (C a₀ * X 0 + C a₁ * X 1 : MvPowerSeries (Fin 2) W) = if j = 0 then a₀ else a₁ := by
  classical
  rw [map_add, coeff_C_mul, coeff_C_mul, coeff_single_X, coeff_single_X]
  fin_cases j <;> simp

theorem constantCoeff_lin (a₀ a₁ : W) :
    constantCoeff (C a₀ * X 0 + C a₁ * X 1 : MvPowerSeries (Fin 2) W) = 0 := by
  simp [constantCoeff_X]

theorem degree_fin_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

end linforms

end DrinfeldCurve.LocalChart.LinearPartAux

set_option maxHeartbeats 4000000 in
open DrinfeldCurve.LocalChart.LinearPartAux MvPowerSeries in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
    (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁}) (hq₁ : (q : W₁) ∈ maximalIdeal W₁)
    (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
    (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
    (W₂ : Type) [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂]
    (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
    (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
    (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
    (ρ : W₁ →+* W₂) (hρ : ρ π₁ = π₂)
    (ψ : (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁}) ≃+*
      (MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}))
    (hψ : ∀ w : W₁, ψ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (ρ w))) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) W₂,
      (∀ i : Fin 2, MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (g i) = 0) ∧
      (∀ i : Fin 2, ψ (Ideal.Quotient.mk _ (MvPowerSeries.X i)) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}) (g i)) ∧
      ∀ a b : W₂, (a ∉ maximalIdeal W₂ ∨ b ∉ maximalIdeal W₂) → a ^ q * b - a * b ^ q ∈ maximalIdeal W₂ →
        ∃ (lam : W₂) (n₀ n₁ : ℕ), IsUnit lam ∧ (n₀ = 1 ∨ (n₀ = 0 ∧ n₁ = 1)) ∧ n₁ < q ∧
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (g 0) * a +
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (g 0) * b - lam * (n₀ : W₂) ∈ maximalIdeal W₂ ∧
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (g 1) * a +
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (g 1) * b - lam * (n₁ : W₂) ∈ maximalIdeal W₂ := by
  classical
  have hprime : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hprime.two_le
  have hπ₁m : π₁ ∈ maximalIdeal W₁ := by rw [hπ₁]; exact Ideal.mem_span_singleton_self _
  have hπ₂m : π₂ ∈ maximalIdeal W₂ := by rw [hπ₂]; exact Ideal.mem_span_singleton_self _
  have hπ₂0 : π₂ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field W₂
    rw [hπ₂, h, Ideal.span_singleton_eq_bot]
  have hf₁0 : constantCoeff f₁ = 0 := constantCoeff_eq_zero_of_sub_drinfeldForm_mem q f₁ hf₁
  have hf₂0 : constantCoeff f₂ = 0 := constantCoeff_eq_zero_of_sub_drinfeldForm_mem q f₂ hf₂

  have memI₁ : ∀ g : MvPowerSeries (Fin 2) W₁, g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}) ↔ constantCoeff g = 0 := fun g => mem_span_X_iff_constantCoeff g
  have memI₂ : ∀ g : MvPowerSeries (Fin 2) W₂, g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ↔ constantCoeff g = 0 := fun g => mem_span_X_iff_constantCoeff g

  have hXnu : ∀ i : Fin 2, ¬ IsUnit (ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (X i))) := by
    intro i hu
    have h' := hu.map ψ.symm
    rw [RingEquiv.symm_apply_apply] at h'
    exact not_isUnit_mk_of_constantCoeff_mem π₁ hπ₁m f₁ u₁ v₁ hf₁0 (X i)
      (by rw [constantCoeff_X]; exact zero_mem _) h'
  choose g hg0 hgψ using fun i => exists_rep_constantCoeff_eq_zero π₂ hπ₂ f₂ u₂ v₂ hv₂ hf₂0 _ (hXnu i)
  have hgI : ∀ i, g i ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) := fun i => (memI₂ _).mpr (hg0 i)
  refine ⟨g, fun i => by rw [coeff_zero_eq_constantCoeff_apply]; exact hg0 i, fun i => (hgψ i).symm, ?_⟩
  intro a b hab hdir

  set M : Fin 2 → Fin 2 → W₂ := fun k i => coeff (Finsupp.single k 1) (g i) with hM
  set lin : Fin 2 → MvPowerSeries (Fin 2) W₂ := fun i => C (M 0 i) * X 0 + C (M 1 i) * X 1 with hlin
  have hlinI : ∀ i, lin i ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) := fun i => (memI₂ _).mpr (constantCoeff_lin _ _)
  have hglin : ∀ i, g i - lin i ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ 2 := by
    intro i
    refine (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W₂ 2 _).mpr fun n hn => ?_
    rcases eq_of_deg_lt_two n hn with rfl | rfl | rfl
    · rw [coeff_zero_eq_constantCoeff_apply, map_sub, hg0 i, constantCoeff_lin, sub_zero]
    · rw [map_sub, coeff_single_lin]; simp [hM]
    · rw [map_sub, coeff_single_lin]; simp [hM]

  have hle : ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}))).map ψ.toRingHom ≤ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) := by
    rw [Ideal.map_map, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · show ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (X 0)) ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂})))
      rw [← hgψ 0]; exact Ideal.mem_map_of_mem _ (hgI 0)
    · show ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (X 1)) ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂})))
      rw [← hgψ 1]; exact Ideal.mem_map_of_mem _ (hgI 1)
  have hψK : ∀ n : ℕ, ∀ s ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}))) ^ n, ψ s ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) ^ n := by
    intro n s hs
    have h1 : ψ.toRingHom s ∈ (((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}))) ^ n).map ψ.toRingHom := Ideal.mem_map_of_mem _ hs
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle n h1
  have hψK1 : ∀ s ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}))), ψ s ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) := fun s hs => hle (Ideal.mem_map_of_mem ψ.toRingHom hs)
  have mkone₁ : ∀ g, g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}) → Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) g ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}))) := fun g hg => Ideal.mem_map_of_mem _ hg
  have mkone₂ : ∀ g, g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) → Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) g ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) := fun g hg => Ideal.mem_map_of_mem _ hg
  have mkK₁ : ∀ n g, g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}) ^ n → Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) g ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}))) ^ n := fun n g hg => mk_mem_map_pow_of_mem_pow (Ideal.span {C π₁ * v₁ - f₁ * u₁}) n g hg
  have mkK₂ : ∀ n g, g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ n → Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) g ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) ^ n := fun n g hg => mk_mem_map_pow_of_mem_pow (Ideal.span {C π₂ * v₂ - f₂ * u₂}) n g hg

  have stepE : ∀ k : Fin 2, ∃ N₀ N₁ : W₂, ∀ j : Fin 2,
      (if j = k then (1 : W₂) else 0) - (M j 0 * N₀ + M j 1 * N₁) ∈ maximalIdeal W₂ := by
    intro k

    have hnu : ¬ IsUnit (ψ.symm (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (X k))) := by
      intro hu
      have h' := hu.map ψ
      rw [RingEquiv.apply_symm_apply] at h'
      exact not_isUnit_mk_of_constantCoeff_mem π₂ hπ₂m f₂ u₂ v₂ hf₂0 (X k)
        (by rw [constantCoeff_X]; exact zero_mem _) h'
    obtain ⟨h, hh0, hhψ⟩ := exists_rep_constantCoeff_eq_zero π₁ hπ₁ f₁ u₁ v₁ hv₁ hf₁0 _ hnu
    have hhI : h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}) := (memI₁ _).mpr hh0
    obtain ⟨τ₀, τ₁, hτ⟩ := Ideal.mem_span_pair.mp hhI
    refine ⟨ρ (constantCoeff τ₀), ρ (constantCoeff τ₁), ?_⟩

    have hτK : ∀ τ : MvPowerSeries (Fin 2) W₁,
        ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) τ) - Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ (constantCoeff τ))) ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) := by
      intro τ
      have h1 : τ - C (constantCoeff τ) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₁), X 1}) := (memI₁ _).mpr (by simp)
      have h2 := hψK1 _ (mkone₁ _ h1)
      rw [map_sub, map_sub, hψ] at h2
      exact h2

    obtain ⟨G, hG⟩ : ∃ G : MvPowerSeries (Fin 2) W₂,
        G = X k - (C (ρ (constantCoeff τ₀)) * lin 0 + C (ρ (constantCoeff τ₁)) * lin 1) := ⟨_, rfl⟩
    have hGI : G ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ 1 := by
      rw [pow_one]; refine (memI₂ _).mpr ?_
      simp [hG, hlin, constantCoeff_X]
    have hGmk : Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) G ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) ^ (1 + 1) := by

      have e1 : Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (X k) =
          ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) τ₀) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 0) + ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) τ₁) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 1) := by
        have h3 := congrArg ψ hhψ
        rw [RingEquiv.apply_symm_apply, ← hτ] at h3
        rw [← h3]
        simp only [map_add, map_mul, ← hgψ]
      have e2 : Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) G =
          (ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) τ₀) - Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ (constantCoeff τ₀)))) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 0)
          + (ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) τ₁) - Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ (constantCoeff τ₁)))) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 1)
          + (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ (constantCoeff τ₀))) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 0 - lin 0)
            + Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ (constantCoeff τ₁))) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 1 - lin 1)) := by
        rw [hG, map_sub, e1]; simp only [map_add, map_mul, map_sub]; ring
      rw [e2, pow_two]
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.add_mem _ ?_ ?_)
      · exact Ideal.mul_mem_mul (hτK τ₀) (mkone₂ _ (hgI 0))
      · exact Ideal.mul_mem_mul (hτK τ₁) (mkone₂ _ (hgI 1))
      · rw [← pow_two]; exact Ideal.mul_mem_left _ _ (mkK₂ 2 _ (hglin 0))
      · rw [← pow_two]; exact Ideal.mul_mem_left _ _ (mkK₂ 2 _ (hglin 1))
    intro j
    have hc := coeff_mem_span_of_mk_mem_pow_succ π₂ hπ₂0 f₂ u₂ v₂ hv₂ hf₂0 1 G hGI hGmk (Finsupp.single j 1)
      (by fin_cases j <;> simp)
    rw [← hπ₂] at hc
    have e3 : coeff (Finsupp.single j 1) G =
        (if j = k then (1 : W₂) else 0) - (M j 0 * ρ (constantCoeff τ₀) + M j 1 * ρ (constantCoeff τ₁)) := by
      rw [hG, map_sub, coeff_single_X, map_add, coeff_C_mul, coeff_C_mul]
      simp only [hlin, coeff_single_lin]
      fin_cases j <;> simp <;> ring
    rw [e3] at hc
    exact hc

  set ℓ : Fin 2 → W₂ := fun i => M 0 i * a + M 1 i * b with hℓ
  have stepF : ℓ 0 * ℓ 1 ^ q - ℓ 0 ^ q * ℓ 1 ∈ maximalIdeal W₂ := by
    obtain ⟨vU₁, hvU₁⟩ := hv₁
    obtain ⟨vU₂, hvU₂⟩ := id hv₂
    set vi₁ : MvPowerSeries (Fin 2) W₁ := ((vU₁⁻¹ : (MvPowerSeries (Fin 2) W₁)ˣ) : MvPowerSeries (Fin 2) W₁) with hvi₁
    set vi₂ : MvPowerSeries (Fin 2) W₂ := ((vU₂⁻¹ : (MvPowerSeries (Fin 2) W₂)ˣ) : MvPowerSeries (Fin 2) W₂) with hvi₂
    have hvvi₁ : v₁ * vi₁ = 1 := by rw [hvi₁, ← hvU₁]; exact Units.mul_inv vU₁
    have hvvi₂ : v₂ * vi₂ = 1 := by rw [hvi₂, ← hvU₂]; exact Units.mul_inv vU₂

    set c₁ : W₁ := constantCoeff (u₁ * vi₁) with hc₁
    set c₂ : W₂ := constantCoeff (u₂ * vi₂) with hc₂
    have hc₁u : IsUnit c₁ := by
      rw [hc₁]; exact isUnit_iff_constantCoeff.mp (hu₁.mul (by rw [hvi₁]; exact Units.isUnit _))
    have hc₂u : IsUnit c₂ := by
      rw [hc₂]; exact isUnit_iff_constantCoeff.mp (hu₂.mul (by rw [hvi₂]; exact Units.isUnit _))

    have hdecomp : ∀ {V : Type} [CommRing V] (f' u' vi : MvPowerSeries (Fin 2) V)
        (hf' : f' - DrinfeldCurve.LocalChart.drinfeldForm q V ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) V), X 1}) ^ (q + 2)),
        f' * u' * vi - C (constantCoeff (u' * vi)) * DrinfeldCurve.LocalChart.drinfeldForm q V ∈
          (Ideal.span {(X 0 : MvPowerSeries (Fin 2) V), X 1}) ^ (q + 2) := by
      intro V _ f' u' vi hf'
      have e : f' * u' * vi - C (constantCoeff (u' * vi)) * DrinfeldCurve.LocalChart.drinfeldForm q V =
          (f' - DrinfeldCurve.LocalChart.drinfeldForm q V) * (u' * vi) +
          DrinfeldCurve.LocalChart.drinfeldForm q V * (u' * vi - C (constantCoeff (u' * vi))) := by ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf') ?_
      have h1 : u' * vi - C (constantCoeff (u' * vi)) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) V), X 1}) ^ 1 := by
        rw [pow_one]; exact (mem_span_X_iff_constantCoeff _).mpr (by simp)
      have := Ideal.mul_mem_mul (drinfeldForm_mem_pow (W := V) q) h1
      rwa [← pow_add] at this
    have hr₁ := hdecomp f₁ u₁ vi₁ hf₁
    have hr₂ := hdecomp f₂ u₂ vi₂ hf₂

    have eπ₁ : Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (C π₁) = Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (f₁ * u₁ * vi₁) := by
      rw [Ideal.Quotient.eq]
      refine Ideal.mem_span_singleton'.mpr ⟨vi₁, ?_⟩
      linear_combination (C π₁) * hvvi₁
    have eπ₂ : Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C π₂) = Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (f₂ * u₂ * vi₂) := by
      rw [Ideal.Quotient.eq]
      refine Ideal.mem_span_singleton'.mpr ⟨vi₂, ?_⟩
      linear_combination (C π₂) * hvvi₂
    have eψπ : ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (f₁ * u₁ * vi₁)) = Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (f₂ * u₂ * vi₂) := by
      rw [← eπ₁, ← eπ₂, hψ, hρ]

    have eψF : ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (DrinfeldCurve.LocalChart.drinfeldForm q W₁)) =
        Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 0 * g 1 ^ q - g 0 ^ q * g 1) := by
      show ψ (Ideal.Quotient.mk _ (X 0 * X 1 ^ q - X 0 ^ q * X 1)) = _
      simp only [map_sub, map_mul, map_pow]
      rw [← hgψ 0, ← hgψ 1]

    obtain ⟨Flin, hFlin⟩ : ∃ Flin : MvPowerSeries (Fin 2) W₂, Flin = lin 0 * lin 1 ^ q - lin 0 ^ q * lin 1 := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : MvPowerSeries (Fin 2) W₂,
        G = C (ρ c₁) * Flin - C c₂ * DrinfeldCurve.LocalChart.drinfeldForm q W₂ := ⟨_, rfl⟩
    have hFg : (g 0 * g 1 ^ q - g 0 ^ q * g 1) - Flin ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ (q + 2) := by
      have h1 := mul_pow_sub_mul_pow_mem (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) (g 0) (lin 0) (g 1) (lin 1) (hlinI 0) (hgI 1) (hlinI 1) (hglin 0) (hglin 1) q (le_trans one_le_two hq2)
      have h2 := mul_pow_sub_mul_pow_mem (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) (g 1) (lin 1) (g 0) (lin 0) (hlinI 1) (hgI 0) (hlinI 0) (hglin 1) (hglin 0) q (le_trans one_le_two hq2)
      have e : (g 0 * g 1 ^ q - g 0 ^ q * g 1) - Flin = (g 0 * g 1 ^ q - lin 0 * lin 1 ^ q) - (g 1 * g 0 ^ q - lin 1 * lin 0 ^ q) := by
        rw [hFlin]; ring
      rw [e]; exact Ideal.sub_mem _ h1 h2
    have hGI : G ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ (q + 1) := by
      rw [hG]
      refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ (drinfeldForm_mem_pow q))
      rw [hFlin]
      refine Ideal.sub_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul (show lin 0 ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ 1 by rw [pow_one]; exact hlinI 0) (Ideal.pow_mem_pow (hlinI 1) q)
        rwa [← pow_add, add_comm] at this
      · have := Ideal.mul_mem_mul (Ideal.pow_mem_pow (hlinI 0) q) (show lin 1 ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}) ^ 1 by rw [pow_one]; exact hlinI 1)
        rwa [← pow_add] at this
    have hGmk : Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) G ∈ ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₂), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}))) ^ (q + 1 + 1) := by

      have eCF : ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (C c₁ * DrinfeldCurve.LocalChart.drinfeldForm q W₁)) =
          Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ c₁)) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 0 * g 1 ^ q - g 0 ^ q * g 1) := by
        rw [map_mul, map_mul, hψ, eψF]
      have eψr : ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (f₁ * u₁ * vi₁ - C c₁ * DrinfeldCurve.LocalChart.drinfeldForm q W₁)) =
          Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (f₂ * u₂ * vi₂)
            - Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ c₁)) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (g 0 * g 1 ^ q - g 0 ^ q * g 1) := by
        rw [map_sub, map_sub, eψπ, eCF]
      have e : Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) G =
          Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (f₂ * u₂ * vi₂ - C c₂ * DrinfeldCurve.LocalChart.drinfeldForm q W₂)
          - ψ (Ideal.Quotient.mk (Ideal.span {C π₁ * v₁ - f₁ * u₁}) (f₁ * u₁ * vi₁ - C c₁ * DrinfeldCurve.LocalChart.drinfeldForm q W₁))
          - Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) (C (ρ c₁)) * Ideal.Quotient.mk (Ideal.span {C π₂ * v₂ - f₂ * u₂}) ((g 0 * g 1 ^ q - g 0 ^ q * g 1) - Flin) := by
        rw [eψr, hG]
        simp only [map_sub, map_mul, map_pow]
        ring
      rw [e, show q + 1 + 1 = q + 2 by ring]
      refine Ideal.sub_mem _ (Ideal.sub_mem _ (mkK₂ _ _ hr₂) (hψK _ _ (mkK₁ _ _ hr₁))) ?_
      exact Ideal.mul_mem_left _ _ (mkK₂ _ _ hFg)
    have hcoef : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 = q + 1 → coeff n G ∈ maximalIdeal W₂ := by
      intro n hn
      rw [hπ₂]
      exact coeff_mem_span_of_mk_mem_pow_succ π₂ hπ₂0 f₂ u₂ v₂ hv₂ hf₂0 (q + 1) G hGI hGmk n hn

    obtain ⟨L, hL⟩ : ∃ L : Fin 2 → MvPolynomial (Fin 2) W₂, L = fun i =>
        MvPolynomial.C (M 0 i) * MvPolynomial.X 0 + MvPolynomial.C (M 1 i) * MvPolynomial.X 1 := ⟨_, rfl⟩
    obtain ⟨Gp, hGp⟩ : ∃ Gp : MvPolynomial (Fin 2) W₂, Gp =
        MvPolynomial.C (ρ c₁) * (L 0 * L 1 ^ q - L 0 ^ q * L 1)
          - MvPolynomial.C c₂ * (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) := ⟨_, rfl⟩
    have hGpG : MvPolynomial.coeToMvPowerSeries.ringHom Gp = G := by
      simp only [hGp, hG, hFlin, hlin, hL, map_sub, map_mul, map_pow, map_add,
        MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X]
      unfold DrinfeldCurve.LocalChart.drinfeldForm
      rfl
    have hhomL : ∀ i, (L i).IsHomogeneous 1 := fun i => by
      rw [hL]; exact (MvPolynomial.isHomogeneous_C_mul_X _ _).add (MvPolynomial.isHomogeneous_C_mul_X _ _)
    have hhomGp : Gp.IsHomogeneous (q + 1) := by
      have h1 : (L 0 * L 1 ^ q - L 0 ^ q * L 1).IsHomogeneous (q + 1) := by
        have a1 := (hhomL 0).mul ((hhomL 1).pow q)
        have a2 := ((hhomL 0).pow q).mul (hhomL 1)
        rw [show 1 + 1 * q = q + 1 by ring] at a1
        rw [show 1 * q + 1 = q + 1 by ring] at a2
        exact a1.sub a2
      have h2 : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) W₂).IsHomogeneous (q + 1) := by
        have a1 := (MvPolynomial.isHomogeneous_X W₂ (0 : Fin 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := W₂) (1 : Fin 2) q)
        have a2 := (MvPolynomial.isHomogeneous_X_pow (R := W₂) (0 : Fin 2) q).mul (MvPolynomial.isHomogeneous_X W₂ (1 : Fin 2))
        rw [add_comm] at a1
        exact a1.sub a2
      rw [hGp]; exact (h1.C_mul _).sub (h2.C_mul _)
    obtain ⟨x, hx⟩ : ∃ x : Fin 2 → W₂, x = fun i => if i = 0 then a else b := ⟨_, rfl⟩
    have heval_mem : MvPolynomial.eval x Gp ∈ maximalIdeal W₂ := by
      rw [MvPolynomial.eval_eq']
      refine Ideal.sum_mem _ fun d hd => Ideal.mul_mem_right _ _ ?_
      by_cases hdeg : d 0 + d 1 = q + 1
      · have := hcoef d hdeg
        rwa [← hGpG, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe] at this
      · rw [hhomGp.coeff_eq_zero (by rw [degree_fin_two]; exact hdeg)]
        exact zero_mem _
    have heval : MvPolynomial.eval x Gp =
        ρ c₁ * (ℓ 0 * ℓ 1 ^ q - ℓ 0 ^ q * ℓ 1) - c₂ * (a * b ^ q - a ^ q * b) := by
      simp [hGp, hL, hℓ, hx, MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [heval] at heval_mem
    have hdir' : c₂ * (a * b ^ q - a ^ q * b) ∈ maximalIdeal W₂ := by
      refine Ideal.mul_mem_left _ _ ?_
      rw [show a * b ^ q - a ^ q * b = -(a ^ q * b - a * b ^ q) by ring]
      exact Submodule.neg_mem _ hdir
    have := Ideal.add_mem _ heval_mem hdir'
    rw [sub_add_cancel] at this
    exact (Ideal.unit_mul_mem_iff_mem _ (hc₁u.map ρ)).mp this

  set κ := ResidueField W₂ with hκ
  set res : W₂ →+* κ := residue W₂ with hres
  have hresm : ∀ w : W₂, w ∈ maximalIdeal W₂ ↔ res w = 0 := fun w => (residue_eq_zero_iff w).symm
  haveI : CharP κ q := (CharP.charP_iff_prime_eq_zero hprime).mpr (by
    have := (hresm _).mp hq₂; simpa using this)
  set α := res (ℓ 0) with hα
  set β := res (ℓ 1) with hβ
  have hFres : α * β ^ q = α ^ q * β := by
    have := (hresm _).mp stepF
    rw [map_sub, map_mul, map_mul, map_pow, map_pow] at this
    exact sub_eq_zero.mp this

  have hnz : α ≠ 0 ∨ β ≠ 0 := by
    obtain ⟨N₀₀, N₁₀, hN0⟩ := stepE 0
    obtain ⟨N₀₁, N₁₁, hN1⟩ := stepE 1
    have e00 := (hresm _).mp (hN0 0)
    have e10 := (hresm _).mp (hN0 1)
    have e01 := (hresm _).mp (hN1 0)
    have e11 := (hresm _).mp (hN1 1)
    simp only [map_sub, map_add, map_mul, map_one, map_zero, if_pos, if_neg, Fin.one_eq_zero_iff,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero, if_true, if_false] at e00 e10 e01 e11
    have ha : res a = α * res N₀₀ + β * res N₁₀ := by
      simp only [hα, hβ, hℓ, map_add, map_mul]
      linear_combination (res a) * e00 + (res b) * e10
    have hb : res b = α * res N₀₁ + β * res N₁₁ := by
      simp only [hα, hβ, hℓ, map_add, map_mul]
      linear_combination (res a) * e01 + (res b) * e11
    by_contra hcon
    push_neg at hcon
    obtain ⟨hα0, hβ0⟩ := hcon
    rw [hα0, hβ0, zero_mul, zero_mul, add_zero] at ha hb
    rcases hab with h | h
    · exact h ((hresm a).mpr ha)
    · exact h ((hresm b).mpr hb)
  have hunit_of_res : ∀ w : W₂, res w ≠ 0 → IsUnit w := by
    intro w hw
    by_contra hu
    exact hw ((hresm w).mp ((mem_maximalIdeal w).mpr hu))
  by_cases hα0 : α = 0
  · have hβ0 : β ≠ 0 := hnz.resolve_left (not_not.mpr hα0)
    refine ⟨ℓ 1, 0, 1, hunit_of_res _ hβ0, Or.inr ⟨rfl, rfl⟩, Nat.lt_of_lt_of_le one_lt_two hq2, ?_, ?_⟩
    · change ℓ 0 - ℓ 1 * ((0 : ℕ) : W₂) ∈ maximalIdeal W₂
      rw [Nat.cast_zero, mul_zero, sub_zero]; exact (hresm _).mpr hα0
    · change ℓ 1 - ℓ 1 * ((1 : ℕ) : W₂) ∈ maximalIdeal W₂
      rw [Nat.cast_one, mul_one, sub_self]; exact zero_mem _
  · set μ := β / α with hμ
    have hμq : μ ^ q = μ := by
      rw [hμ, div_pow, div_eq_div_iff (pow_ne_zero _ hα0) hα0]
      linear_combination hFres
    obtain ⟨n, hnq, hnμ⟩ := exists_natCast_eq_of_pow_eq q κ μ hμq
    refine ⟨ℓ 0, 1, n, hunit_of_res _ hα0, Or.inl rfl, hnq, ?_, ?_⟩
    · change ℓ 0 - ℓ 0 * ((1 : ℕ) : W₂) ∈ maximalIdeal W₂
      rw [Nat.cast_one, mul_one, sub_self]; exact zero_mem _
    · change ℓ 1 - ℓ 0 * ((n : ℕ) : W₂) ∈ maximalIdeal W₂
      refine (hresm _).mpr ?_
      rw [map_sub, map_mul, map_natCast, hnμ, hμ, ← hα, ← hβ, ← mul_div_assoc, mul_div_cancel_left₀ β hα0, sub_self]

end S_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C (solution)
