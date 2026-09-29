-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f8a7338f-cb80-596d-aa9b-879666aedadb

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Theorems.Thm_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient
import Theorems.Thm_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
import Theorems.Thm_Multiset_esymm_map_sub_esymm_map_mem_pow_succ
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul
import Theorems.Thm_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart

set_option autoImplicit false

p2m_open "IsLocalRing FormalGroup P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart.FormalGroup"

namespace FormalGroup
p2m_export "FormalGroup" "mk map coeToPowerSeries eval nthSeries linCombAdic drinfeldDivisorAdic IsDrinfeldBasisAdic isDrinfeldBasisAdic_iff linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero"
namespace HasseCoreAux
p2m_open "FormalGroup"

open MvPowerSeries

theorem memSpanX_iff {W : Type} [CommRing W] (g : MvPowerSeries (Fin 2) W) :
    g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ↔ constantCoeff g = 0 := by
  have := MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 1 g
  rw [pow_one] at this
  rw [this]
  constructor
  · intro h; rw [← coeff_zero_eq_constantCoeff_apply]; exact h 0 (by simp)
  · intro h n hn
    have : n = 0 := by ext i; fin_cases i <;> simp <;> omega
    rw [this, coeff_zero_eq_constantCoeff_apply]; exact h

theorem coeff_drinfeldForm_eq_zero_of_lt {W : Type} [CommRing W] (q : ℕ) [Fact q.Prime] (n : Fin 2 →₀ ℕ)
    (h : n 0 + n 1 < q + 1) : coeff n (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
  classical
  have e1 : (X 0 : MvPowerSeries (Fin 2) W) * X 1 ^ q = monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  have e2 : (X 0 : MvPowerSeries (Fin 2) W) ^ q * X 1 = monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  unfold DrinfeldCurve.LocalChart.drinfeldForm
  rw [e1, e2, map_sub, coeff_monomial, coeff_monomial, if_neg, if_neg, sub_zero]
  · intro hn; subst hn; simp at h
  · intro hn; subst hn; simp at h

theorem drinfeldForm_mem_pow {W : Type} [CommRing W] (q : ℕ) [Fact q.Prime] :
    DrinfeldCurve.LocalChart.drinfeldForm q W ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 1) :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 1) _).mpr
    (fun n hn => coeff_drinfeldForm_eq_zero_of_lt q n hn)

section chart

variable {W : Type} [CommRing W] [IsLocalRing W]

theorem mem_map_span_X_iff_not_isUnit (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v) (hf : constantCoeff f = 0)
    (x : MvPowerSeries (Fin 2) W ⧸ Ideal.span {C π * v - f * u}) :
    x ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}))
      ↔ ¬ IsUnit x := by
  classical
  have hπm : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self _
  constructor
  · intro hx hunit
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    have hg0 : constantCoeff g = 0 := (memSpanX_iff g).mp hg
    set φ : MvPowerSeries (Fin 2) W →+* ResidueField W := (residue W).comp constantCoeff with hφ
    have hker : ∀ a ∈ Ideal.span {C π * v - f * u}, φ a = 0 := by
      intro a ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [hφ, RingHom.coe_comp, Function.comp_apply, map_mul, map_sub, constantCoeff_C, hf, zero_mul, sub_zero]
      rw [(residue_eq_zero_iff π).mpr hπm]; simp
    have h1 := hunit.map (Ideal.Quotient.lift _ φ hker)
    rw [Ideal.Quotient.lift_mk] at h1
    simp only [hφ, RingHom.coe_comp, Function.comp_apply] at h1
    rw [hg0, map_zero] at h1
    exact not_isUnit_zero h1
  · intro hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hc : constantCoeff g ∈ maximalIdeal W := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu'
      exact hx ((isUnit_iff_constantCoeff.mpr hu').map _)
    rw [hπ] at hc
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hc
    obtain ⟨vU, hvU⟩ := hv
    have hfI : f ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := (memSpanX_iff f).mpr hf
    have hCπ : Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) (C π) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π * v - f * u})) := by
      have e : Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) (C π) =
          Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) (f * u * ↑vU⁻¹) := by
        rw [Ideal.Quotient.eq]
        refine Ideal.mem_span_singleton'.mpr ⟨↑vU⁻¹, ?_⟩
        have hvv : v * ↑vU⁻¹ = 1 := by rw [← hvU]; exact Units.mul_inv vU
        linear_combination (C π) * hvv
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hfI))
    have hgsplit : g = (g - C (constantCoeff g)) + C w * C π := by rw [← map_mul, hw]; ring
    have hgI : g - C (constantCoeff g) ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} :=
      (memSpanX_iff _).mpr (by simp)
    rw [hgsplit, map_add, map_mul]
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ hgI) (Ideal.mul_mem_left _ _ hCπ)

omit [IsLocalRing W] in

theorem mk_C_mem_pow (q : ℕ) [Fact q.Prime] (π : W)
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2)) :
    Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) (C π) ∈
      ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}))) ^ (q + 1) := by
  obtain ⟨vU, hvU⟩ := hv
  have e : Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) (C π) =
      Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) (f * u * ↑vU⁻¹) := by
    rw [Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton'.mpr ⟨↑vU⁻¹, ?_⟩
    have hvv : v * ↑vU⁻¹ = 1 := by rw [← hvU]; exact Units.mul_inv vU
    linear_combination (C π) * hvv
  have hfI : f ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 1) := by
    have e2 : f = (f - DrinfeldCurve.LocalChart.drinfeldForm q W) + DrinfeldCurve.LocalChart.drinfeldForm q W := by ring
    rw [e2]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ _) hf) (drinfeldForm_mem_pow q)
  rw [e, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hfI))

end chart

section chart2

variable {W : Type} [CommRing W] [IsLocalRing W]

theorem isUnit_constantCoeff_of_isUnit_mk (π : W) (hπ : π ∈ maximalIdeal W)
    (f u v : MvPowerSeries (Fin 2) W) (hf : constantCoeff f = 0) (g : MvPowerSeries (Fin 2) W)
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) g)) : IsUnit (constantCoeff g) := by
  set φ : MvPowerSeries (Fin 2) W →+* ResidueField W := (residue W).comp constantCoeff with hφ
  have hker : ∀ a ∈ Ideal.span {C π * v - f * u}, φ a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [hφ, RingHom.coe_comp, Function.comp_apply, map_mul, map_sub, constantCoeff_C, hf, zero_mul, sub_zero]
    rw [(residue_eq_zero_iff π).mpr hπ]; simp
  have h1 := hg.map (Ideal.Quotient.lift _ φ hker)
  rw [Ideal.Quotient.lift_mk] at h1
  simp only [hφ, RingHom.coe_comp, Function.comp_apply] at h1
  by_contra hnu
  have hm : constantCoeff g ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hnu
  rw [(residue_eq_zero_iff _).mpr hm] at h1
  exact not_isUnit_zero h1

end chart2

theorem degree_fin_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem coeff_mul_of_forall_coeff_eq_zero {W : Type} [CommRing W] (d : ℕ) (G H : MvPowerSeries (Fin 2) W)
    (hH : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < d → coeff n H = 0) (m : Fin 2 →₀ ℕ) (hm : m 0 + m 1 = d) :
    coeff m (G * H) = constantCoeff G * coeff m H := by
  classical
  rw [coeff_mul, ← Finset.sum_erase_add _ _ (show ((0 : Fin 2 →₀ ℕ), m) ∈ Finset.HasAntidiagonal.antidiagonal m by simp)]
  rw [Finset.sum_eq_zero, _root_.zero_add, coeff_zero_eq_constantCoeff_apply]
  intro p hp
  rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨hne, hsum⟩ := hp
  have hp2 : p.2 0 + p.2 1 < d := by
    have h0 : p.1 ≠ 0 := by
      intro h; apply hne; ext <;> simp [h, ← hsum]
    have : 0 < p.1 0 + p.1 1 := by
      by_contra hc
      push_neg at hc
      apply h0; ext i; fin_cases i <;> simp <;> omega
    have e0 := congrArg (fun n : Fin 2 →₀ ℕ => n 0) hsum
    have e1 := congrArg (fun n : Fin 2 →₀ ℕ => n 1) hsum
    simp only [Finsupp.coe_add, Pi.add_apply] at e0 e1
    omega
  rw [hH p.2 hp2, mul_zero]

theorem map_esymm {A B : Type} [CommRing A] [CommRing B] {Fh : Type} [FunLike Fh A B] [RingHomClass Fh A B]
    (φ : Fh) {ι : Type} (s : Finset ι) (g : ι → A) (k : ℕ) :
    φ ((s.val.map g).esymm k) = (s.val.map (fun i => φ (g i))).esymm k := by
  classical
  rw [Finset.esymm_map_val, Finset.esymm_map_val, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_prod]

theorem prod_X_sub_C_eq_multiset {A : Type} [CommRing A] {ι : Type} (s : Finset ι) (g : ι → A) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (g i))) = ((s.val.map g).map fun t => Polynomial.X - Polynomial.C t).prod := by
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl

theorem coeff_prod_X_sub_C {A : Type} [CommRing A] {ι : Type} (s : Finset ι) (g : ι → A) (k : ℕ) (hk : k ≤ s.card) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (g i))).coeff k = (-1) ^ (s.card - k) * (s.val.map g).esymm (s.card - k) := by
  rw [prod_X_sub_C_eq_multiset]
  have hcard : Multiset.card (s.val.map g) = s.card := by simp
  rw [Multiset.prod_X_sub_C_coeff (s.val.map g) (by rw [hcard]; exact hk), hcard]

theorem esymm_mem_pow {A : Type} [CommRing A] (I : Ideal A) {ι : Type} (s : Finset ι) (g : ι → A)
    (hg : ∀ i ∈ s, g i ∈ I) (k : ℕ) : (s.val.map g).esymm k ∈ I ^ k := by
  classical
  rw [Finset.esymm_map_val]
  refine Ideal.sum_mem _ fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htk⟩ := ht
  rw [← htk]
  clear htk
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Ideal.mul_mem_mul (hg a (hts (Finset.mem_insert_self a t)))
      (ih fun i hi => hts (Finset.mem_insert_of_mem hi))

theorem antidiag_snd_lt (q i j : ℕ) (h : i + j = q) (hne : i = 0 → j = q → False) : j < q := by
  rcases Nat.lt_or_ge j q with hj | hj
  · exact hj
  · exact (hne (by omega) (by omega)).elim

theorem sum_coeff_mul_pow_eq_eval {W : Type} [CommRing W] (d : ℕ) (Hp : MvPolynomial (Fin 2) W)
    (hH : Hp.IsHomogeneous d) (a b : W) :
    ∑ i ∈ Finset.range (d + 1),
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) Hp * a ^ i * b ^ (d - i)
      = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a else b) Hp := by
  classical
  set φ : ℕ → (Fin 2 →₀ ℕ) := fun i => Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i) with hφ
  have hφ0 : ∀ i, φ i 0 = i := by intro i; simp [hφ]
  have hφ1 : ∀ i, φ i 1 = d - i := by intro i; simp [hφ]
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two]
  simp only [Fin.isValue, ↓reduceIte, show ¬ ((1 : Fin 2) = 0) from by decide]
  have hinj : ∀ i ∈ Finset.range (d + 1), ∀ j ∈ Finset.range (d + 1), φ i = φ j → i = j := by
    intro i _ j _ hij; have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hij; simpa [hφ0] using this
  have step : ∑ i ∈ Finset.range (d + 1), MvPolynomial.coeff (φ i) Hp * a ^ i * b ^ (d - i) =
      ∑ m ∈ (Finset.range (d + 1)).image φ, MvPolynomial.coeff m Hp * (a ^ m 0 * b ^ m 1) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hφ0, hφ1, mul_assoc]
  rw [step]
  symm
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_image]
    have hdeg : m.degree = d := by
      by_contra h; exact (MvPolynomial.mem_support_iff.mp hm) (hH.coeff_eq_zero h)
    rw [degree_fin_two] at hdeg
    refine ⟨m 0, Finset.mem_range.mpr (by omega), ?_⟩
    ext i; fin_cases i
    · simp [hφ]
    · simp [hφ]; omega
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem mul_mem_pow_add' {S : Type} [CommRing S] (K : Ideal S) {a b : S} {m n : ℕ}
    (ha : a ∈ K ^ m) (hb : b ∈ K ^ n) : a * b ∈ K ^ (m + n) := by
  rw [pow_add]; exact Ideal.mul_mem_mul ha hb

theorem pow_mem_pow_mul' {S : Type} [CommRing S] (K : Ideal S) {a : S} {m : ℕ} (ha : a ∈ K ^ m) (n : ℕ) :
    a ^ n ∈ K ^ (m * n) := by
  rw [pow_mul]; exact Ideal.pow_mem_pow ha n

end FormalGroup.HasseCoreAux

set_option maxHeartbeats 6400000 in
open FormalGroup.HasseCoreAux in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R]
    (F : FormalGroup R)
    (x₀ x₁ : R) (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (T : R) (hT : ∃ w : R, IsUnit w ∧ PowerSeries.coeff q (F.nthSeries q) - w * T ∈ Ideal.span {(q : R)})

    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (ε : W) (hε : IsUnit ε) (hπq : π ^ (q - 1) = ε * (q : W))
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u})
    (he₀ : e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0)) (he₁ : e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1)) :
    ∃ (h : MvPowerSeries (Fin 2) W)
      (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q * (q - 1))),
      (∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
          a ^ q * b - a * b ^ q ∈ maximalIdeal W →
          IsUnit (∑ i ∈ Finset.range (q * (q - 1) + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i)) h
              * a ^ i * b ^ (q * (q - 1) - i))) ∧
      e T = Ideal.Quotient.mk _ h := by
  classical

  have hprime : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hprime.two_le
  have hq1 : 1 ≤ q := hprime.one_lt.le
  have hq0 : q ≠ 0 := hprime.ne_zero
  have hqq : q ≤ q * q := Nat.le_mul_self q
  have hdN : q * (q - 1) = q * q - q := Nat.mul_sub_one q q
  have hq21 : (q + 1) * (q - 1) = q * q - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact (Nat.sub_eq_of_eq_add (by ring)).symm
  have hdeep1 : q * (q - 1) + 1 ≤ (q + 1) * (q - 1) := by
    rw [hq21, hdN]
    have : q + 2 ≤ q * q := by nlinarith
    omega
  have hNq : q * q ≠ q := by nlinarith
  have hA1 : ∀ j, j < q → q * (q - 1) + 1 ≤ q * q - j ∧ j ≤ q * q := by
    intro j hj; rw [hdN]; constructor <;> omega
  have hA3 : q * (q - 1) + 1 ≤ (q + 1) + (q * q - q) := by rw [hdN]; omega
  have hEven : Even (q * q - q) := by
    rw [← hdN, show q * (q - 1) = (q - 1) * ((q - 1) + 1) by rw [Nat.sub_add_cancel hq1, mul_comm]]
    exact Nat.even_mul_succ_self _
  have hneg1R : ((-1 : R)) ^ (q * q - q) = 1 := hEven.neg_one_pow
  have hneg1W : ((-1 : MvPolynomial (Fin 2) W)) ^ (q * q - q) = 1 := hEven.neg_one_pow

  have hπm : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self _
  have hπ0 : π ≠ 0 := by
    intro h; apply IsDiscreteValuationRing.not_a_field (R := W); rw [hπ, h, Ideal.span_singleton_eq_bot]
  obtain ⟨εU, hεU⟩ := hε
  have hqW : (q : W) ∈ maximalIdeal W := by
    have e1 : (q : W) = ↑εU⁻¹ * π ^ (q - 1) := by
      rw [hπq, ← hεU, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e1, show q - 1 = (q - 2) + 1 by omega, pow_succ, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ hπm
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h1 := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 2) _).mp hf 0 (by simp)
    rw [map_sub, coeff_drinfeldForm_eq_zero_of_lt q 0 (by simp), sub_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
    exact h1

  have hK : ∀ x, x ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ↔ ¬ IsUnit x :=
    fun x => mem_map_span_X_iff_not_isUnit π hπ f u v hv hf0 x
  have hKpow : ∀ n g, g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ n → Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) g ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ n := by
    intro n g hg; rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hg
  have hKpow' : ∀ n s, s ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ n → ∃ g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ n, Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) g = s := by
    intro n s hs; rw [← Ideal.map_pow] at hs
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hs
  have hCπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (MvPowerSeries.C π) ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q + 1) :=
    mk_C_mem_pow q π f u v hv hf
  have hCq : (q : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q * (q - 1) + 1) := by
    have e1 : (q : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (MvPowerSeries.C (↑εU⁻¹ : W)) * (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (MvPowerSeries.C π)) ^ (q - 1) := by
      rw [← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_natCast (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})),
        ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := W))]
      congr 2
      rw [hπq, ← hεU, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e1]
    refine Ideal.pow_le_pow_right hdeep1 (Ideal.mul_mem_left _ _ ?_)
    exact pow_mem_pow_mul' _ hCπ (q - 1)

  have hunit_e : ∀ x : R, IsUnit (e x) ↔ IsUnit x := by
    intro x; constructor
    · intro h; have := h.map e.symm; simpa using this
    · intro h; exact h.map e
  have hmR : ∀ x : R, x ∈ maximalIdeal R ↔ e x ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) := by
    intro x; rw [hK, hunit_e, mem_maximalIdeal, mem_nonunits_iff]
  have hx₀ : x₀ ∈ maximalIdeal R := by
    rw [hmR, he₀]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hx₁ : x₁ ∈ maximalIdeal R := by
    rw [hmR, he₁]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hmap_e : (maximalIdeal R).map e.toRingHom = ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hy
      exact (hmR x).mp hx
    · intro y hy
      have : y = e.toRingHom (e.symm y) := by simp
      rw [this]
      refine Ideal.mem_map_of_mem _ ?_
      rw [hmR]; simpa using hy
  have hepow : ∀ n x, x ∈ maximalIdeal R ^ n → e x ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ n := by
    intro n x hx
    have h1 : e.toRingHom x ∈ (maximalIdeal R ^ n).map e.toRingHom := Ideal.mem_map_of_mem _ hx
    rw [Ideal.map_pow, hmap_e] at h1
    exact h1

  have hmaxS : (maximalIdeal (MvPowerSeries (Fin 2) W)).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})) = ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [hK]
      intro hu'
      have h1 := isUnit_constantCoeff_of_isUnit_mk π hπm f u v hf0 g hu'
      exact (mem_maximalIdeal _).mp hg (MvPowerSeries.isUnit_iff_constantCoeff.mpr h1)
    · intro y hy
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine Ideal.mem_map_of_mem _ ?_
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hg
      exact (hK _).mp hy (hg.map _)
  haveI hcomplete : IsAdicComplete (maximalIdeal R) R := by
    have h0 := (MvPowerSeries.isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient W 2 (Ideal.span {MvPowerSeries.C π * v - f * u})).2
    rw [hmaxS, ← hmap_e] at h0
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal R) e).mp h0

  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin q × Fin q → R, ℓ = fun pt => F.linCombAdic (maximalIdeal R) x₀ x₁ pt.1 pt.2 := ⟨_, rfl⟩
  have hℓmem : ∀ pt, ℓ pt ∈ maximalIdeal R := by
    intro pt; rw [hℓ]
    exact (FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero R (maximalIdeal R) F
      x₀ x₁ hx₀ hx₁ pt.1 pt.2).1
  have hℓlin : ∀ pt, ℓ pt - (((pt.1 : ℕ) : R) * x₀ + ((pt.2 : ℕ) : R) * x₁) ∈ maximalIdeal R ^ 2 := by
    intro pt; rw [hℓ]
    exact (FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero R (maximalIdeal R) F
      x₀ x₁ hx₀ hx₁ pt.1 pt.2).2.1

  obtain ⟨U, hU, hfac⟩ := (FormalGroup.isDrinfeldBasisAdic_iff F (maximalIdeal R) q x₀ x₁).mp hD
  have hDdiv : F.drinfeldDivisorAdic (maximalIdeal R) q x₀ x₁ =
      Polynomial.coeToPowerSeries.ringHom (∏ pt : Fin q × Fin q, (Polynomial.X - Polynomial.C (ℓ pt))) := by
    rw [Fintype.prod_prod_type, map_prod]
    show (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
        (PowerSeries.X - PowerSeries.C (F.linCombAdic (maximalIdeal R) x₀ x₁ a b))) = _
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_prod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [hℓ, map_sub]
    congr 1
    · exact Polynomial.coe_X.symm
    · exact (Polynomial.coe_C _).symm
  obtain ⟨P, hP⟩ : ∃ P : Polynomial R, P = ∏ pt : Fin q × Fin q, (Polynomial.X - Polynomial.C (ℓ pt)) := ⟨_, rfl⟩
  have hcardN : (Finset.univ : Finset (Fin q × Fin q)).card = q * q := by simp
  have hPcoeff : ∀ j, j ≤ q * q → P.coeff j =
      (-1) ^ (q * q - j) * ((Finset.univ : Finset (Fin q × Fin q)).val.map ℓ).esymm (q * q - j) := by
    intro j hj
    rw [hP, coeff_prod_X_sub_C _ _ _ (by rw [hcardN]; exact hj), hcardN]
  have hcoefq : PowerSeries.coeff q (F.nthSeries q) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal q, PowerSeries.coeff ij.1 U * P.coeff ij.2 := by
    rw [hfac, hDdiv, ← hP, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun ij _ => ?_
    congr 1
    exact Polynomial.coeff_coe P ij.2

  obtain ⟨ι, hι⟩ : ∃ ι : MvPolynomial (Fin 2) W →+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u},
      ι = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})).comp MvPolynomial.coeToMvPowerSeries.ringHom := ⟨_, rfl⟩
  obtain ⟨lin, hlin⟩ : ∃ lin : Fin q × Fin q → MvPolynomial (Fin 2) W, lin = fun pt =>
      ((pt.1 : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 0 + ((pt.2 : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 1 := ⟨_, rfl⟩
  have hιX : ∀ i, ι (MvPolynomial.X i) = Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (MvPowerSeries.X i) := by
    intro i; rw [hι, RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]
  have heℓ : ∀ pt, e (ℓ pt) - ι (lin pt) ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ 2 := by
    intro pt
    have h1 := hepow 2 _ (hℓlin pt)
    rw [map_sub] at h1
    have e2 : e (((pt.1 : ℕ) : R) * x₀ + ((pt.2 : ℕ) : R) * x₁) = ι (lin pt) := by
      rw [map_add, map_mul, map_mul, map_natCast, map_natCast, he₀, he₁, hlin]
      simp only [map_add, map_mul, map_natCast, hιX]
    rw [← e2]; exact h1
  have hιlinK : ∀ pt, ι (lin pt) ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) := by
    intro pt
    have : ι (lin pt) = e (ℓ pt) - (e (ℓ pt) - ι (lin pt)) := by ring
    rw [this]
    exact Ideal.sub_mem _ ((hmR _).mp (hℓmem pt)) (Ideal.pow_le_self two_ne_zero (heℓ pt))

  have hes : ∀ k, ((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => e (ℓ pt))).esymm k
      - ((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => ι (lin pt))).esymm k ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (k + 1) :=
    fun k => Multiset.esymm_map_sub_esymm_map_mem_pow_succ _ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) _ Finset.univ (fun pt => e (ℓ pt)) (fun pt => ι (lin pt))
      (fun pt _ => hιlinK pt) (fun pt _ => heℓ pt) k
  have hesK : ∀ k, ((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => e (ℓ pt))).esymm k ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ k :=
    fun k => esymm_mem_pow ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) Finset.univ (fun pt => e (ℓ pt)) (fun pt _ => (hmR _).mp (hℓmem pt)) k

  obtain ⟨E, hE⟩ := DrinfeldCurve.LocalChart.exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul q W π hπ hqW
  obtain ⟨Hp, hHp⟩ : ∃ Hp : MvPolynomial (Fin 2) W, Hp = ∑ i ∈ Finset.range (q + 1),
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) W) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i)) := ⟨_, rfl⟩
  obtain ⟨PW, hPW⟩ : ∃ PW : Polynomial (MvPolynomial (Fin 2) W),
      PW = ∏ pt : Fin q × Fin q, (Polynomial.X - Polynomial.C (lin pt)) := ⟨_, rfl⟩
  have hPWE : PW = Polynomial.X ^ (q ^ 2) - Polynomial.C Hp * Polynomial.X ^ q
      + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) W) * MvPolynomial.X 1 ^ q
          - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X
      + Polynomial.C (MvPolynomial.C π) * E := by
    rw [hPW, hlin]
    simp only [Fintype.prod_prod_type]
    rw [hHp]; exact hE
  have hPWq : PW.coeff q = -Hp + MvPolynomial.C π * E.coeff q := by
    rw [hPWE]
    have hne1 : q ≠ q ^ 2 := by rw [sq]; exact hNq.symm
    have hne2 : (1 : ℕ) ≠ q := hprime.one_lt.ne
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, if_neg hne1, if_neg hne2, if_true, mul_one, eq_self_iff_true]
    ring
  have hPWcoeff : PW.coeff q = (-1) ^ (q * q - q) * ((Finset.univ : Finset (Fin q × Fin q)).val.map lin).esymm (q * q - q) := by
    rw [hPW, coeff_prod_X_sub_C _ _ _ (by rw [hcardN]; exact hqq), hcardN]

  have hesW : ((Finset.univ : Finset (Fin q × Fin q)).val.map lin).esymm (q * q - q) =
      -Hp + MvPolynomial.C π * E.coeff q := by
    rw [← hPWq, hPWcoeff, hneg1W, one_mul]

  have hlinhom : ∀ pt, (lin pt).IsHomogeneous 1 := by
    intro pt; rw [hlin]
    have a1 : (((pt.1 : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 0).IsHomogeneous 1 := by
      rw [← map_natCast (MvPolynomial.C : W →+* MvPolynomial (Fin 2) W)]
      exact MvPolynomial.isHomogeneous_C_mul_X _ _
    have a2 : (((pt.2 : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 1).IsHomogeneous 1 := by
      rw [← map_natCast (MvPolynomial.C : W →+* MvPolynomial (Fin 2) W)]
      exact MvPolynomial.isHomogeneous_C_mul_X _ _
    exact a1.add a2
  have heshom : (((Finset.univ : Finset (Fin q × Fin q)).val.map lin).esymm (q * q - q)).IsHomogeneous (q * q - q) := by
    rw [Finset.esymm_map_val]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun t ht => ?_
    rw [Finset.mem_powersetCard] at ht
    have := MvPolynomial.IsHomogeneous.prod t (fun pt => lin pt) (fun _ => 1) (fun pt _ => hlinhom pt)
    rw [Finset.sum_const, smul_eq_mul, mul_one, ht.2] at this
    exact this
  have hHphom : Hp.IsHomogeneous (q * q - q) := by
    rw [hHp]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have := (MvPolynomial.isHomogeneous_X_pow (R := W) (0 : Fin 2) ((q - 1) * i)).mul
      (MvPolynomial.isHomogeneous_X_pow (R := W) (1 : Fin 2) ((q - 1) * (q - i)))
    have e1 : (q - 1) * i + (q - 1) * (q - i) = q * q - q := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hi', ← hdN, mul_comm]
    rw [e1] at this; exact this

  have hGdef : MvPolynomial.C π * E.coeff q = ((Finset.univ : Finset (Fin q × Fin q)).val.map lin).esymm (q * q - q) + Hp := by
    rw [hesW]; ring
  have hGhom : (MvPolynomial.C π * E.coeff q).IsHomogeneous (q * q - q) := by
    rw [hGdef]; exact heshom.add hHphom
  have hEq : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < q * q - q → MvPolynomial.coeff n (E.coeff q) = 0 := by
    intro n hn
    have h1 := hGhom.coeff_eq_zero (d := n) (by rw [degree_fin_two]; exact Nat.ne_of_lt hn)
    rw [MvPolynomial.coeff_C_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hπ0
  have hEqmem : ((E.coeff q : MvPolynomial (Fin 2) W) : MvPowerSeries (Fin 2) W) ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q * q - q) := by
    refine (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W _ _).mpr fun n hn => ?_
    rw [MvPolynomial.coeff_coe]; exact hEq n hn
  have hιG : ι (MvPolynomial.C π * E.coeff q) ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q * (q - 1) + 1) := by
    rw [map_mul, hι, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]
    have h1 := mul_mem_pow_add' _ hCπ (hKpow _ _ hEqmem)
    exact Ideal.pow_le_pow_right hA3 h1

  have hDq : e (P.coeff q) + ι Hp ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q * (q - 1) + 1) := by
    rw [hPcoeff q hqq, hneg1R, one_mul, map_esymm]
    have h1 := hes (q * q - q)
    have h2 : ((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => ι (lin pt))).esymm (q * q - q) =
        ι (((Finset.univ : Finset (Fin q × Fin q)).val.map lin).esymm (q * q - q)) := by
      rw [map_esymm]
    have e3 : ((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => e (ℓ pt))).esymm (q * q - q) + ι Hp
        = ((((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => e (ℓ pt))).esymm (q * q - q))
            - ((Finset.univ : Finset (Fin q × Fin q)).val.map (fun pt => ι (lin pt))).esymm (q * q - q))
          + ι (MvPolynomial.C π * E.coeff q) := by
      rw [h2, hGdef, map_add]; ring
    rw [e3, hdN]
    refine Ideal.add_mem _ h1 ?_
    rw [← hdN]; exact hιG
  have hmain : e (PowerSeries.coeff q (F.nthSeries q)) + e (PowerSeries.coeff 0 U) * ι Hp ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q * (q - 1) + 1) := by
    rw [hcoefq, map_sum]
    rw [← Finset.add_sum_erase _ _ (show ((0 : ℕ), q) ∈ Finset.HasAntidiagonal.antidiagonal q by simp)]
    rw [map_mul, show e (PowerSeries.coeff 0 U) * e (P.coeff q) + (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal q).erase (0, q),
        e (PowerSeries.coeff x.1 U * P.coeff x.2)) + e (PowerSeries.coeff 0 U) * ι Hp
      = e (PowerSeries.coeff 0 U) * (e (P.coeff q) + ι Hp) + ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal q).erase (0, q),
        e (PowerSeries.coeff x.1 U * P.coeff x.2) by ring]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hDq) (Ideal.sum_mem _ fun ij hij => ?_)
    rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hij
    obtain ⟨hne, hsum⟩ := hij
    have hj : ij.2 < q := antidiag_snd_lt q ij.1 ij.2 hsum (fun h1 h2 => hne (Prod.ext h1 h2))
    rw [map_mul, hPcoeff ij.2 (hA1 ij.2 hj).2, map_mul, map_pow, map_neg, map_one, map_esymm]
    refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.pow_le_pow_right (hA1 ij.2 hj).1 (hesK _)

  obtain ⟨w, hw, hwT⟩ := hT
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hwT
  have hwT' : e (w * T) + e (PowerSeries.coeff 0 U) * ι Hp ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q * (q - 1) + 1) := by
    have e1 : e (w * T) = e (PowerSeries.coeff q (F.nthSeries q)) - e r * (q : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) := by
      rw [← map_natCast e, ← map_mul, hr, ← map_sub]; congr 1; ring
    rw [e1, show e (PowerSeries.coeff q (F.nthSeries q)) - e r * (q : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u})
        + e (PowerSeries.coeff 0 U) * ι Hp
      = (e (PowerSeries.coeff q (F.nthSeries q)) + e (PowerSeries.coeff 0 U) * ι Hp)
        - e r * (q : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) by ring]
    exact Ideal.sub_mem _ hmain (Ideal.mul_mem_left _ _ hCq)

  have hU0 : IsUnit (PowerSeries.coeff 0 U) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact PowerSeries.isUnit_constantCoeff U hU
  obtain ⟨wU, hwU⟩ := hw
  obtain ⟨σ, hσ⟩ : ∃ σ : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}, σ = -(e (↑wU⁻¹ : R) * e (PowerSeries.coeff 0 U)) := ⟨_, rfl⟩
  have hσu : IsUnit σ := by
    rw [hσ]; exact ((Units.isUnit wU⁻¹).map e |>.mul (hU0.map e)).neg
  have heT : e T - σ * ι Hp ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}))) ^ (q * (q - 1) + 1) := by
    have e1 : e T - σ * ι Hp = e (↑wU⁻¹ : R) * (e (w * T) + e (PowerSeries.coeff 0 U) * ι Hp) := by
      have hinv : e (↑wU⁻¹ : R) * e (↑wU : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rw [hσ, ← hwU, map_mul]
      linear_combination (-(e T)) * hinv
    rw [e1]; exact Ideal.mul_mem_left _ _ hwT'
  obtain ⟨Gσ, hGσ⟩ := Ideal.Quotient.mk_surjective σ
  have hGσu : IsUnit (MvPowerSeries.constantCoeff Gσ) :=
    isUnit_constantCoeff_of_isUnit_mk π hπm f u v hf0 Gσ (by rw [hGσ]; exact hσu)
  obtain ⟨k, hk, hkeq⟩ := hKpow' _ _ heT

  have hHpmem : ((Hp : MvPolynomial (Fin 2) W) : MvPowerSeries (Fin 2) W) ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q * (q - 1)) := by
    refine (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W _ _).mpr fun n hn => ?_
    rw [MvPolynomial.coeff_coe]
    exact hHphom.coeff_eq_zero (by rw [degree_fin_two, ← hdN]; exact Nat.ne_of_lt hn)
  have hιHp : ι Hp = Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) ((Hp : MvPolynomial (Fin 2) W) : MvPowerSeries (Fin 2) W) := by
    rw [hι, RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  refine ⟨Gσ * ((Hp : MvPolynomial (Fin 2) W) : MvPowerSeries (Fin 2) W) + k, ?_, ?_, ?_⟩
  · exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hHpmem) (Ideal.pow_le_pow_right (Nat.le_succ _) hk)
  · intro a b hab hdir

    have hcoef : ∀ i ∈ Finset.range (q * (q - 1) + 1),
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i))
          (Gσ * ((Hp : MvPolynomial (Fin 2) W) : MvPowerSeries (Fin 2) W) + k) =
        MvPowerSeries.constantCoeff Gσ * MvPolynomial.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i)) Hp := by
      intro i hi
      have hi' : i ≤ q * (q - 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hdeg : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i)) 0 +
          (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i)) 1 = q * (q - 1) := by
        simp [Nat.add_sub_cancel' hi']
      rw [map_add, coeff_mul_of_forall_coeff_eq_zero (q * (q - 1)) Gσ _ (fun n hn => by
          rw [MvPolynomial.coeff_coe]; exact hHphom.coeff_eq_zero (by rw [degree_fin_two, ← hdN]; exact Nat.ne_of_lt hn)) _ hdeg,
        MvPolynomial.coeff_coe,
        (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W _ k).mp hk _ (by rw [hdeg]; exact Nat.lt_succ_self _), _root_.add_zero]
    rw [Finset.sum_congr rfl (fun i hi => by rw [hcoef i hi])]

    have hsum : ∑ i ∈ Finset.range (q * (q - 1) + 1),
        MvPowerSeries.constantCoeff Gσ * MvPolynomial.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i)) Hp
          * a ^ i * b ^ (q * (q - 1) - i)
        = MvPowerSeries.constantCoeff Gσ * ∑ i ∈ Finset.range (q + 1), a ^ ((q - 1) * i) * b ^ ((q - 1) * (q - i)) := by
      have hev : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a else b) Hp =
          ∑ i ∈ Finset.range (q + 1), a ^ ((q - 1) * i) * b ^ ((q - 1) * (q - i)) := by
        rw [hHp]; simp [MvPolynomial.eval_X]
      have hHphom' : Hp.IsHomogeneous (q * (q - 1)) := by rw [hdN]; exact hHphom
      rw [← hev, ← sum_coeff_mul_pow_eq_eval _ Hp hHphom' a b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum]
    exact hGσu.mul (DrinfeldCurve.LocalChart.isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal q W hqW a b hab hdir)
  · rw [map_add, map_mul, hGσ, ← hιHp, hkeq]; ring

end S_FormalGroup_IsDrinfeldBasisAdic_exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart (solution)
