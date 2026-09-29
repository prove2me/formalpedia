-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d6ee080f-e372-55e3-a95d-80a3b3ffb666

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal

set_option autoImplicit false
set_option maxHeartbeats 400000000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

namespace BlowupFibreSol

attribute [local instance] Classical.propDecidable

section Filtration

variable {O : Type} [CommRing O]

def F (I : Ideal O) (m n : ℕ) : Ideal (MvPowerSeries (Fin 2) O) where
  carrier := {G | ∀ e : Fin 2 →₀ ℕ, coeff e G ∈ I ^ (n - m * e.degree)}
  add_mem' {f g} hf hg e := by
    rw [map_add]; exact Ideal.add_mem _ (hf e) (hg e)
  zero_mem' e := by
    rw [map_zero]; exact Ideal.zero_mem _
  smul_mem' s f hf e := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have hpe : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hdeg : p.2.degree ≤ e.degree := by
      rw [← hpe, map_add]; exact Nat.le_add_left _ _
    have hle : I ^ (n - m * p.2.degree) ≤ I ^ (n - m * e.degree) :=
      Ideal.pow_le_pow_right (by
        have := Nat.mul_le_mul_left m hdeg
        omega)
    exact Ideal.mul_mem_left _ _ (hle (hf p.2))

theorem mem_F {I : Ideal O} {m n : ℕ} {G : MvPowerSeries (Fin 2) O} :
    G ∈ F I m n ↔ ∀ e : Fin 2 →₀ ℕ, coeff e G ∈ I ^ (n - m * e.degree) := Iff.rfl

theorem F_antitone (I : Ideal O) (m : ℕ) {n n' : ℕ} (h : n ≤ n') : F I m n' ≤ F I m n := by
  intro G hG e
  exact Ideal.pow_le_pow_right (by omega) (hG e)

theorem F_zero (I : Ideal O) (m : ℕ) : F I m 0 = ⊤ := by
  ext G; simp [mem_F]

theorem mul_mem_F {I : Ideal O} {m a b : ℕ} {G H : MvPowerSeries (Fin 2) O}
    (hG : G ∈ F I m a) (hH : H ∈ F I m b) : G * H ∈ F I m (a + b) := by
  classical
  intro e
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hpe : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = e.degree := by rw [← hpe, map_add]
  have hprod : coeff p.1 G * coeff p.2 H ∈ I ^ ((a - m * p.1.degree) + (b - m * p.2.degree)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul (hG p.1) (hH p.2)
  refine Ideal.pow_le_pow_right ?_ hprod
  have hm' : m * e.degree = m * p.1.degree + m * p.2.degree := by rw [← hdeg, Nat.mul_add]
  generalize m * p.1.degree = x at hm' ⊢
  generalize m * p.2.degree = y at hm' ⊢
  omega

theorem pow_mem_F {I : Ideal O} {m a : ℕ} {G : MvPowerSeries (Fin 2) O} (hG : G ∈ F I m a) (k : ℕ) :
    G ^ k ∈ F I m (a * k) := by
  induction k with
  | zero => rw [pow_zero, mul_zero, F_zero]; trivial
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact mul_mem_F ih hG

theorem C_mem_F {I : Ideal O} {m k : ℕ} {c : O} (hc : c ∈ I ^ k) : (C c : MvPowerSeries (Fin 2) O) ∈ F I m k := by
  classical
  intro e
  rw [coeff_C]
  split_ifs with he
  · subst he; simpa using hc
  · exact Ideal.zero_mem _

theorem C_mem_F_zero (I : Ideal O) (m : ℕ) (c : O) : (C c : MvPowerSeries (Fin 2) O) ∈ F I m 0 := by
  rw [F_zero]; trivial

theorem X_mem_F (I : Ideal O) (m : ℕ) (i : Fin 2) : (X i : MvPowerSeries (Fin 2) O) ∈ F I m m := by
  classical
  intro e
  rw [coeff_X]
  split_ifs with he
  · subst he
    rw [Finsupp.degree_single, mul_one, Nat.sub_self, pow_zero, Ideal.one_eq_top]; trivial
  · exact Ideal.zero_mem _

theorem span_X_le_F : Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1} ≤ F (⊥ : Ideal O) 1 1 := by
  rw [Ideal.span_le]
  rintro _ (rfl | rfl)
  · exact X_mem_F ⊥ 1 0
  · exact X_mem_F ⊥ 1 1

theorem span_X_pow_le_F (n : ℕ) : (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ n ≤ F (⊥ : Ideal O) 1 n := by
  induction n with
  | zero => rw [F_zero]; exact le_top
  | succ n ih =>
    intro G hG
    rw [pow_succ] at hG
    refine Submodule.mul_induction_on hG (fun a ha b hb => ?_) (fun a b ha hb => Ideal.add_mem _ ha hb)
    exact mul_mem_F (ih ha) (span_X_le_F hb)

theorem coeff_eq_zero_of_mem_span_X_pow {n : ℕ} {G : MvPowerSeries (Fin 2) O}
    (hG : G ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ n) (e : Fin 2 →₀ ℕ) (he : e.degree < n) :
    coeff e G = 0 := by
  have h := span_X_pow_le_F n hG e
  rw [one_mul] at h
  have hk : n - e.degree ≠ 0 := by omega
  have := Ideal.pow_le_self hk h
  rwa [Ideal.mem_bot] at this

end Filtration

section Generic

variable {O : Type} [CommRing O]

theorem mem_span_X_of_constantCoeff_eq_zero (g : MvPowerSeries (Fin 2) O) (hg : constantCoeff g = 0) :
    g ∈ Ideal.span ({X 0, X 1} : Set (MvPowerSeries (Fin 2) O)) := by
  classical
  let g₁ : MvPowerSeries (Fin 2) O := fun m => if m 0 = 0 then g m else 0
  have hcoeff : ∀ m, coeff m g₁ = if m 0 = 0 then coeff m g else 0 := fun m => rfl
  have h1 : (X 1 : MvPowerSeries (Fin 2) O) ∣ g₁ := by
    rw [X_dvd_iff]
    intro m hm1
    rw [hcoeff]
    split_ifs with hm0
    · have : m = 0 := by
        ext i; fin_cases i
        · simpa using hm0
        · simpa using hm1
      rw [this, coeff_zero_eq_constantCoeff_apply, hg]
    · rfl
  have h0 : (X 0 : MvPowerSeries (Fin 2) O) ∣ (g - g₁) := by
    rw [X_dvd_iff]
    intro m hm0
    rw [map_sub, hcoeff, if_pos hm0, sub_self]
  have : g = (g - g₁) + g₁ := by ring
  rw [this]
  obtain ⟨t₀, ht₀⟩ := h0
  obtain ⟨t₁, ht₁⟩ := h1
  refine Ideal.add_mem _ ?_ ?_
  · rw [ht₀]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [ht₁]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem sub_C_constantCoeff_mem {A : Type} [CommRing A] (ψ : MvPowerSeries (Fin 2) O →+* A)
    (P : Ideal A) (h0 : ψ (X 0) ∈ P) (h1 : ψ (X 1) ∈ P)
    (g : MvPowerSeries (Fin 2) O) : ψ g - ψ (C (constantCoeff g)) ∈ P := by
  have hmem := mem_span_X_of_constantCoeff_eq_zero (g - C (constantCoeff g)) (by simp)
  have hle : Ideal.map ψ (Ideal.span ({X 0, X 1} : Set (MvPowerSeries (Fin 2) O))) ≤ P := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact h0
    · exact h1
  have := hle (Ideal.mem_map_of_mem ψ hmem)
  rwa [map_sub] at this

theorem map_span_X_pow_le {A : Type} [CommRing A] (ψ : MvPowerSeries (Fin 2) O →+* A) (t : A)
    (h0 : ψ (X 0) ∈ Ideal.span {t}) (h1 : ψ (X 1) ∈ Ideal.span {t}) (n : ℕ)
    (g : MvPowerSeries (Fin 2) O) (hg : g ∈ Ideal.span ({X 0, X 1} : Set (MvPowerSeries (Fin 2) O)) ^ n) :
    ψ g ∈ Ideal.span {t ^ n} := by
  have hle : Ideal.map ψ (Ideal.span ({X 0, X 1} : Set (MvPowerSeries (Fin 2) O))) ≤ Ideal.span {t} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact h0
    · exact h1
  have := Ideal.pow_right_mono hle n
  rw [← Ideal.map_pow, Ideal.span_singleton_pow] at this
  exact this (Ideal.mem_map_of_mem _ hg)

end Generic

section Chart

variable {q : ℕ} [Fact q.Prime] {O : Type} [CommRing O] {ϖ : O} (pr : ChartPresentation q O ϖ)

theorem constantCoeff_drinfeldForm : constantCoeff (drinfeldForm q O) = 0 := by
  simp [drinfeldForm, constantCoeff_X]

theorem coeff_drinfeldForm_eq_zero_of_degree_lt (e : Fin 2 →₀ ℕ) (he : e.degree < q + 1) :
    coeff e (drinfeldForm q O) = 0 := by
  classical
  have h1 : (X 0 * X 1 ^ q : MvPowerSeries (Fin 2) O) = monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [X_pow_eq, X, monomial_mul_monomial, one_mul]
  have h2 : (X 0 ^ q * X 1 : MvPowerSeries (Fin 2) O) = monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq, X, monomial_mul_monomial, one_mul]
  rw [drinfeldForm, map_sub, h1, h2, coeff_monomial, coeff_monomial, if_neg, if_neg, sub_zero]
  · rintro rfl
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single] at he; omega
  · rintro rfl
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single] at he; omega

theorem coeff_f_eq_zero_of_degree_lt (e : Fin 2 →₀ ℕ) (he : e.degree < q + 1) : coeff e pr.f = 0 := by
  have h := coeff_eq_zero_of_mem_span_X_pow pr.f_sub_mem e (by omega)
  rwa [map_sub, coeff_drinfeldForm_eq_zero_of_degree_lt e he, sub_zero] at h

def dm1 (q : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 q
def dm2 (q : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 q + Finsupp.single 1 1

theorem degree_dm1 : (dm1 q).degree = q + 1 := by
  rw [dm1, map_add, Finsupp.degree_single, Finsupp.degree_single]; omega

theorem degree_dm2 : (dm2 q).degree = q + 1 := by
  rw [dm2, map_add, Finsupp.degree_single, Finsupp.degree_single]

omit [Fact q.Prime] in
theorem coeff_drinfeldForm (e : Fin 2 →₀ ℕ) :
    coeff e (drinfeldForm q O) = (if dm1 q = e then 1 else 0) - (if dm2 q = e then 1 else 0) := by
  classical
  have h1 : (X 0 * X 1 ^ q : MvPowerSeries (Fin 2) O) = monomial (dm1 q) 1 := by
    rw [dm1, X_pow_eq, X, monomial_mul_monomial, one_mul]
  have h2 : (X 0 ^ q * X 1 : MvPowerSeries (Fin 2) O) = monomial (dm2 q) 1 := by
    rw [dm2, X_pow_eq, X, monomial_mul_monomial, one_mul]
  rw [drinfeldForm, map_sub, h1, h2, coeff_monomial, coeff_monomial]
  by_cases ha : dm1 q = e <;> by_cases hb : dm2 q = e
  · rw [if_pos ha.symm, if_pos hb.symm, if_pos ha, if_pos hb]
  · rw [if_pos ha.symm, if_neg (Ne.symm hb), if_pos ha, if_neg hb]
  · rw [if_neg (Ne.symm ha), if_pos hb.symm, if_neg ha, if_pos hb]
  · rw [if_neg (Ne.symm ha), if_neg (Ne.symm hb), if_neg ha, if_neg hb]

omit [Fact q.Prime] in
theorem coeff_drinfeldPoly (k : Type) [Field k] (e : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff e (drinfeldPoly q k) = (if dm1 q = e then 1 else 0) - (if dm2 q = e then 1 else 0) := by
  classical
  have h1 : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) k) = MvPolynomial.monomial (dm1 q) 1 := by
    rw [dm1, MvPolynomial.X, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  have h2 : (MvPolynomial.X 0 ^ q * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = MvPolynomial.monomial (dm2 q) 1 := by
    rw [dm2, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  rw [drinfeldPoly, MvPolynomial.coeff_sub, h1, h2, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]

theorem coeff_f_mul_u (e : Fin 2 →₀ ℕ) (he : e.degree ≤ q + 1) :
    coeff e (pr.f * pr.u) = coeff e (drinfeldForm q O) * constantCoeff pr.u := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (e, 0)]
  · rw [coeff_zero_eq_constantCoeff_apply]
    by_cases hlt : e.degree < q + 1
    · rw [coeff_f_eq_zero_of_degree_lt pr e hlt, coeff_drinfeldForm_eq_zero_of_degree_lt e hlt]
    · have hf : coeff e pr.f = coeff e (drinfeldForm q O) := by
        have h := coeff_eq_zero_of_mem_span_X_pow pr.f_sub_mem e (by omega)
        rwa [map_sub, sub_eq_zero] at h
      rw [hf]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hb : b ≠ 0 := by
      rintro rfl; apply hne; rw [add_zero] at hab'; rw [hab']
    have hdeg : a.degree < q + 1 := by
      have h1 : a.degree + b.degree = e.degree := by rw [← hab', map_add]
      have h2 : b.degree ≠ 0 := fun h0 => hb ((Finsupp.degree_eq_zero_iff b).mp h0)
      omega
    rw [coeff_f_eq_zero_of_degree_lt pr a hdeg, zero_mul]
  · intro h
    exfalso; apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_zero]

theorem constantCoeff_f : constantCoeff pr.f = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact coeff_f_eq_zero_of_degree_lt pr 0 (by simp)

end Chart

section Main

variable (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (GaloisField q 2) (ResidueField O)]
    [IsAlgClosed (ResidueField O)] [IsDomain (CoordRing q (ResidueField O))]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (pr : ChartPresentation q O ϖ)
    (hnzd : Ideal.Quotient.mk (Ideal.span {pr.rel}) (C ϖ) ∈ nonZeroDivisors pr.Ring)

include hπ hϖ hϖ0 hnzd in
theorem main :
    let S := pr.Ring
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk _
    let L := Localization.Away (mkS (C ϖ))
    let ι₀ : O →+* L := (algebraMap S L).comp (mkS.comp (C (σ := Fin 2) (R := O)))
    let x₀ : L := algebraMap S L (mkS (X 0)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let x₁ : L := algebraMap S L (mkS (X 1)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let R : Subring L := Subring.closure (Set.range (algebraMap S L) ∪ {x₀, x₁})
    ∃ (hι₀ : ∀ o : O, ι₀ o ∈ R) (hx₀ : x₀ ∈ R) (hx₁ : x₁ ∈ R)
      (P : Ideal ↥R) (_ : P = Ideal.span {(⟨ι₀ π, hι₀ π⟩ : ↥R)})
      (_ : IsNoetherianRing ↥R) (hP : P.IsPrime)
      (algR : Algebra (ResidueField O) (↥R ⧸ P))
      (_ : ∀ a : O, algebraMap (ResidueField O) (↥R ⧸ P) (residue O a) = Ideal.Quotient.mk P ⟨ι₀ a, hι₀ a⟩)
      (eR : (↥R ⧸ P) ≃ₐ[ResidueField O] CoordRing q (ResidueField O))
      (c : ResidueField O),
      (∀ s : S, (∃ a ∈ maximalIdeal O, ∃ g₀ g₁ : MvPowerSeries (Fin 2) O, s = mkS (C a + X 0 * g₀ + X 1 * g₁)) →
        ∃ h : algebraMap S L s ∈ R, (⟨_, h⟩ : ↥R) ∈ P) ∧
      c ≠ 0 ∧
      c ^ (q + 1) * residue O (MvPowerSeries.constantCoeff pr.u) = residue O (MvPowerSeries.constantCoeff pr.v) ∧
      eR (Ideal.Quotient.mk P ⟨x₀, hx₀⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * x q (ResidueField O) ∧
      eR (Ideal.Quotient.mk P ⟨x₁, hx₁⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * y q (ResidueField O) := by
  intro S mkS L ι₀ x₀ x₁ R
  classical

  have hπ0 : π ≠ 0 := by
    rintro rfl
    apply hϖ0
    have h := hϖ
    rw [hπ, Ideal.mem_span_singleton, zero_dvd_iff] at h
    exact h
  have hπirr : Irreducible π := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hπ
  obtain ⟨m, εu, hϖπ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hπirr
  set ε : O := (εu : O) with hεdef
  have hϖε : ϖ = π ^ m * ε := by rw [hϖπ, mul_comm]
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_mul] at hϖε
      have hu : IsUnit ϖ := hϖε ▸ εu.isUnit
      exact (IsLocalRing.mem_maximalIdeal ϖ).mp hϖ hu
    · exact h0
  set κ := ResidueField O with hκdef

  set ϖS : S := mkS (C ϖ) with hϖSdef
  have hpowers : Submonoid.powers ϖS ≤ nonZeroDivisors S := Submonoid.powers_le.mpr hnzd
  haveI : IsLocalization (Submonoid.powers ϖS) L := inferInstance
  set ι : S →+* L := algebraMap S L with hιdef
  have hιinj : Function.Injective ι := IsLocalization.injective L hpowers
  set ϖL : L := ι ϖS with hϖLdef
  have hϖLunit : IsUnit ϖL := IsLocalization.Away.algebraMap_isUnit ϖS
  set inv : L := IsLocalization.Away.invSelf (S := L) ϖS with hinvdef
  have hϖinv : ϖL * inv = 1 := IsLocalization.Away.mul_invSelf ϖS
  have hinvϖ : inv * ϖL = 1 := by rw [mul_comm, hϖinv]

  have hSR : ∀ s : S, ι s ∈ R := fun s => Subring.subset_closure (Or.inl ⟨s, rfl⟩)
  have hι₀ : ∀ o : O, ι₀ o ∈ R := fun o => hSR _
  have hx₀ : x₀ ∈ R := Subring.subset_closure (Or.inr (by simp))
  have hx₁ : x₁ ∈ R := Subring.subset_closure (Or.inr (by simp))
  set ψ : MvPowerSeries (Fin 2) O →+* R := (ι.comp mkS).codRestrict R (fun g => hSR (mkS g)) with hψdef
  have hψ_coe : ∀ g, ((ψ g : R) : L) = ι (mkS g) := fun g => rfl
  set ϖR : R := ψ (C ϖ) with hϖRdef
  set πR : R := ψ (C π) with hπRdef
  have hπR : πR = ⟨ι₀ π, hι₀ π⟩ := rfl
  set x₀R : R := ⟨x₀, hx₀⟩ with hx₀Rdef
  set x₁R : R := ⟨x₁, hx₁⟩ with hx₁Rdef
  have hψX0 : ψ (X 0) = ϖR * x₀R := by
    apply Subtype.ext
    show ι (mkS (X 0)) = ϖL * (ι (mkS (X 0)) * inv)
    rw [mul_left_comm, hϖinv, mul_one]
  have hψX1 : ψ (X 1) = ϖR * x₁R := by
    apply Subtype.ext
    show ι (mkS (X 1)) = ϖL * (ι (mkS (X 1)) * inv)
    rw [mul_left_comm, hϖinv, mul_one]
  set P : Ideal R := Ideal.span {πR} with hPdef
  have hϖRP : ϖR ∈ P := by
    have : ϖR = πR * ψ (C (π ^ (m - 1) * ε)) := by
      rw [hϖRdef, hπRdef, ← map_mul, ← map_mul]
      congr 1
      rw [hϖε, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hψX0P : ψ (X 0) ∈ P := by rw [hψX0]; exact Ideal.mul_mem_right _ _ hϖRP
  have hψX1P : ψ (X 1) ∈ P := by rw [hψX1]; exact Ideal.mul_mem_right _ _ hϖRP
  have hcong : ∀ g : MvPowerSeries (Fin 2) O, ψ g - ψ (C (constantCoeff g)) ∈ P :=
    fun g => sub_C_constantCoeff_mem ψ P hψX0P hψX1P g
  have hψCmem : ∀ a ∈ maximalIdeal O, ψ (C a) ∈ P := by
    intro a ha
    rw [hπ, Ideal.mem_span_singleton'] at ha
    obtain ⟨t, rfl⟩ := ha
    rw [map_mul, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hcen : ∀ s : S, (∃ a ∈ maximalIdeal O, ∃ g₀ g₁ : MvPowerSeries (Fin 2) O,
      s = mkS (C a + X 0 * g₀ + X 1 * g₁)) → ∃ h : ι s ∈ R, (⟨_, h⟩ : R) ∈ P := by
    rintro s ⟨a, ha, g₀, g₁, rfl⟩
    refine ⟨hSR _, ?_⟩
    have : (⟨ι (mkS (C a + X 0 * g₀ + X 1 * g₁)), hSR _⟩ : R) = ψ (C a + X 0 * g₀ + X 1 * g₁) := rfl
    rw [this, map_add, map_add, map_mul, map_mul]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hψCmem a ha) (Ideal.mul_mem_right _ _ hψX0P))
      (Ideal.mul_mem_right _ _ hψX1P)

  set 𝔪 := maximalIdeal O with h𝔪def
  have hϖpow_mem : ∀ k : ℕ, ϖ ^ k ∈ 𝔪 ^ (m * k) := by
    intro k
    rw [hϖε, mul_pow, ← pow_mul, hπ, Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hRform : ∀ r : L, r ∈ R → ∃ (N : ℕ) (B : MvPowerSeries (Fin 2) O),
      B ∈ F 𝔪 m (m * N) ∧ r * ϖL ^ N = ι (mkS B) := by
    intro r hr
    refine Subring.closure_induction (p := fun r _ => ∃ (N : ℕ) (B : MvPowerSeries (Fin 2) O),
      B ∈ F 𝔪 m (m * N) ∧ r * ϖL ^ N = ι (mkS B)) ?_ ?_ ?_ ?_ ?_ ?_ hr
    · rintro z (⟨s, rfl⟩ | hz)
      · obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact ⟨0, G, by rw [mul_zero, F_zero]; trivial, by rw [pow_zero, mul_one]⟩
      · rcases hz with rfl | rfl
        · refine ⟨1, X 0, by rw [mul_one]; exact X_mem_F _ m 0, ?_⟩
          show ι (mkS (X 0)) * inv * ϖL ^ 1 = ι (mkS (X 0))
          rw [pow_one, mul_assoc, hinvϖ, mul_one]
        · refine ⟨1, X 1, by rw [mul_one]; exact X_mem_F _ m 1, ?_⟩
          show ι (mkS (X 1)) * inv * ϖL ^ 1 = ι (mkS (X 1))
          rw [pow_one, mul_assoc, hinvϖ, mul_one]
    · exact ⟨0, 0, Ideal.zero_mem _, by rw [map_zero, map_zero, zero_mul]⟩
    · exact ⟨0, 1, by rw [mul_zero, F_zero]; trivial, by rw [map_one, map_one, pow_zero, one_mul]⟩
    · rintro a b - - ⟨Na, Ba, hBa, ha⟩ ⟨Nb, Bb, hBb, hb⟩
      refine ⟨Na + Nb, Ba * C (ϖ ^ Nb) + Bb * C (ϖ ^ Na), Ideal.add_mem _ ?_ ?_, ?_⟩
      · have := mul_mem_F hBa (C_mem_F (m := m) (hϖpow_mem Nb))
        rwa [← Nat.mul_add] at this
      · have := mul_mem_F hBb (C_mem_F (m := m) (hϖpow_mem Na))
        rwa [← Nat.mul_add, Nat.add_comm] at this
      · rw [add_mul, pow_add, ← mul_assoc, ha, mul_comm (ϖL ^ Na) (ϖL ^ Nb), ← mul_assoc, hb]
        simp only [map_add, map_mul, map_pow]
        rfl
    · rintro a - ⟨Na, Ba, hBa, ha⟩
      exact ⟨Na, -Ba, (F 𝔪 m (m * Na)).neg_mem hBa, by rw [neg_mul, ha, map_neg, map_neg]⟩
    · rintro a b - - ⟨Na, Ba, hBa, ha⟩ ⟨Nb, Bb, hBb, hb⟩
      refine ⟨Na + Nb, Ba * Bb, ?_, ?_⟩
      · have := mul_mem_F hBa hBb
        rwa [← Nat.mul_add] at this
      · rw [pow_add, mul_mul_mul_comm, ha, hb, ← map_mul, ← map_mul]

  set FR : R := x₀R * x₁R ^ q - x₀R ^ q * x₁R with hFRdef
  set uinv : MvPowerSeries (Fin 2) O := ↑(pr.isUnit_u.unit⁻¹) with huinv
  have huu : pr.u * uinv = 1 := by rw [huinv]; exact pr.isUnit_u.mul_val_inv
  set lam : O := constantCoeff (pr.v * uinv) with hlamdef
  have hlam : FR - ψ (C lam) ∈ Ideal.span {ϖR} := by
    have hh := map_span_X_pow_le ψ ϖR (by rw [hψX0]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (by rw [hψX1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) (q + 2) _ pr.f_sub_mem
    rw [Ideal.mem_span_singleton'] at hh
    obtain ⟨rh, hrh⟩ := hh
    set g : MvPowerSeries (Fin 2) O := pr.v * uinv with hgdef

    have hrelS : mkS (C (ϖ ^ (q + 1))) * mkS pr.v = mkS pr.f * mkS pr.u := by
      rw [← map_mul, ← map_mul]
      exact Ideal.Quotient.eq.mpr (by rw [Ideal.mem_span_singleton]; exact ⟨1, by rw [ChartPresentation.rel, mul_one]⟩)
    have hf : ι (mkS pr.f) = ϖL ^ (q + 1) * ι (mkS g) := by
      have huu' : ι (mkS pr.u) * ι (mkS uinv) = 1 := by
        rw [← map_mul, ← map_mul, huu, map_one, map_one]
      have : ι (mkS pr.f) = ι (mkS pr.f) * ι (mkS pr.u) * ι (mkS uinv) := by
        rw [mul_assoc, huu', mul_one]
      rw [this, ← map_mul, ← hrelS, hgdef]
      simp only [map_pow, map_mul, hϖLdef, hϖSdef]
      ring
    have hform : ι (mkS (drinfeldForm q O)) = ϖL ^ (q + 1) * (x₀ * x₁ ^ q - x₀ ^ q * x₁) := by
      have e0 : ι (mkS (X 0)) = ϖL * x₀ := congrArg Subtype.val hψX0
      have e1 : ι (mkS (X 1)) = ϖL * x₁ := congrArg Subtype.val hψX1
      simp only [drinfeldForm, map_sub, map_mul, map_pow]
      rw [e0, e1]; ring
    have hhL : ι (mkS (pr.f - drinfeldForm q O)) = ϖL ^ (q + 2) * (rh : L) := by
      have := congrArg (fun r : R => (r : L)) hrh
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
      rw [← hψ_coe, ← this, mul_comm]; rfl
    have hkey : ι (mkS g) = (x₀ * x₁ ^ q - x₀ ^ q * x₁) + ϖL * rh := by
      have h1 : ι (mkS pr.f) = ι (mkS (drinfeldForm q O)) + ι (mkS (pr.f - drinfeldForm q O)) := by
        rw [map_sub, map_sub]; ring
      rw [hf, hform, hhL] at h1
      have h2 : ϖL ^ (q + 1) * ι (mkS g) = ϖL ^ (q + 1) * ((x₀ * x₁ ^ q - x₀ ^ q * x₁) + ϖL * rh) := by
        rw [h1]; ring
      exact (hϖLunit.pow (q + 1)).mul_left_cancel h2
    have hR : FR = ψ g - ϖR * rh := by
      apply Subtype.ext
      rw [hFRdef]
      push_cast
      rw [hψ_coe, hkey]
      show x₀ * x₁ ^ q - x₀ ^ q * x₁ = x₀ * x₁ ^ q - x₀ ^ q * x₁ + ϖL * ↑rh - ι (mkS (C ϖ)) * ↑rh
      ring
    have : FR - ψ (C lam) = (ψ g - ψ (C (constantCoeff g))) - ϖR * rh := by rw [hR]; ring
    rw [this]
    refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    exact sub_C_constantCoeff_mem ψ _ (by rw [hψX0]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (by rw [hψX1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) g
  have hϖRle : Ideal.span {ϖR} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hϖRP
  have hlamP : FR - ψ (C lam) ∈ P := hϖRle hlam

  have hu0 : IsUnit (constantCoeff pr.u) := (MvPowerSeries.isUnit_iff_constantCoeff).mp pr.isUnit_u
  have hv0 : IsUnit (constantCoeff pr.v) := (MvPowerSeries.isUnit_iff_constantCoeff).mp pr.isUnit_v
  have hlam_mul : lam * constantCoeff pr.u = constantCoeff pr.v := by
    rw [hlamdef, map_mul, mul_assoc, ← map_mul, mul_comm uinv, huu, map_one, mul_one]
  have hlambar_ne : residue O lam ≠ 0 := by
    intro h0
    rw [IsLocalRing.residue_eq_zero_iff] at h0
    have : constantCoeff pr.v ∈ maximalIdeal O := by rw [← hlam_mul]; exact Ideal.mul_mem_right _ _ h0
    exact (IsLocalRing.mem_maximalIdeal _).mp this hv0

  obtain ⟨c, hc⟩ : ∃ c : κ, c ^ (q + 1) = residue O lam := IsAlgClosed.exists_pow_nat_eq _ (by omega)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hc; exact hlambar_ne hc.symm
  have hcrel : c ^ (q + 1) * residue O (constantCoeff pr.u) = residue O (constantCoeff pr.v) := by
    rw [hc, ← map_mul, hlam_mul]

  set φ₀ : O →+* R ⧸ P := (Ideal.Quotient.mk P).comp (ψ.comp (C : O →+* MvPowerSeries (Fin 2) O)) with hφ₀
  have hφ₀ker : ∀ a ∈ maximalIdeal O, φ₀ a = 0 := by
    intro a ha
    show Ideal.Quotient.mk P (ψ (C a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact hψCmem a ha
  letI algR : Algebra κ (R ⧸ P) := (Ideal.Quotient.lift (maximalIdeal O) φ₀ hφ₀ker : κ →+* R ⧸ P).toAlgebra
  have halgR : ∀ a : O, algebraMap κ (R ⧸ P) (residue O a) = Ideal.Quotient.mk P (ψ (C a)) := fun a => rfl
  have halgR' : ∀ a : O, algebraMap κ (R ⧸ P) (residue O a) = Ideal.Quotient.mk P ⟨ι₀ a, hι₀ a⟩ := fun a => rfl

  set CR := CoordRing q κ with hCRdef
  set xb : Fin 2 → R ⧸ P := ![algebraMap κ (R ⧸ P) c⁻¹ * Ideal.Quotient.mk P x₀R,
    algebraMap κ (R ⧸ P) c⁻¹ * Ideal.Quotient.mk P x₁R] with hxb
  have hFbar : Ideal.Quotient.mk P FR = algebraMap κ (R ⧸ P) (c ^ (q + 1)) := by
    rw [hc, halgR]; exact (Ideal.Quotient.eq).mpr hlamP
  have hkill : MvPolynomial.aeval xb (drinfeldPoly q κ - 1) = 0 := by
    have hcinv : algebraMap κ (R ⧸ P) c⁻¹ ^ (q + 1) * algebraMap κ (R ⧸ P) (c ^ (q + 1)) = 1 := by
      rw [← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ hc0, one_pow, map_one]
    simp only [map_sub, map_one, drinfeldPoly, map_mul, map_pow, MvPolynomial.aeval_X, hxb,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have : Ideal.Quotient.mk P x₀R * Ideal.Quotient.mk P x₁R ^ q -
        Ideal.Quotient.mk P x₀R ^ q * Ideal.Quotient.mk P x₁R = Ideal.Quotient.mk P FR := by
      simp only [hFRdef, map_sub, map_mul, map_pow]
    rw [sub_eq_zero]
    calc _ = algebraMap κ (R ⧸ P) c⁻¹ ^ (q + 1) * (Ideal.Quotient.mk P x₀R * Ideal.Quotient.mk P x₁R ^ q -
        Ideal.Quotient.mk P x₀R ^ q * Ideal.Quotient.mk P x₁R) := by ring
      _ = 1 := by rw [this, hFbar, hcinv]
  set θ : CR →ₐ[κ] R ⧸ P := Ideal.Quotient.liftₐ (drinfeldIdeal q κ) (MvPolynomial.aeval xb) (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨t, rfl⟩ := ha
      rw [map_mul, hkill, mul_zero]) with hθdef
  have hθmk : ∀ pp : MvPolynomial (Fin 2) κ, θ (DrinfeldCurve.mk q κ pp) = MvPolynomial.aeval xb pp := fun pp => rfl
  have hθx : θ (x q κ) = algebraMap κ (R ⧸ P) c⁻¹ * Ideal.Quotient.mk P x₀R := by
    show θ (DrinfeldCurve.mk q κ (MvPolynomial.X 0)) = _
    rw [hθmk, MvPolynomial.aeval_X, hxb]; rfl
  have hθy : θ (y q κ) = algebraMap κ (R ⧸ P) c⁻¹ * Ideal.Quotient.mk P x₁R := by
    show θ (DrinfeldCurve.mk q κ (MvPolynomial.X 1)) = _
    rw [hθmk, MvPolynomial.aeval_X, hxb]; rfl
  have hθcx : Ideal.Quotient.mk P x₀R = θ (algebraMap κ CR c * x q κ) := by
    rw [map_mul, hθx, AlgHom.commutes, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
  have hθcy : Ideal.Quotient.mk P x₁R = θ (algebraMap κ CR c * y q κ) := by
    rw [map_mul, hθy, AlgHom.commutes, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

  have hθsurj : Function.Surjective θ := by
    have hrange : ∀ r : R, Ideal.Quotient.mk P r ∈ θ.range := by
      intro r
      obtain ⟨rL, hrL⟩ := r
      refine Subring.closure_induction (p := fun z hz => Ideal.Quotient.mk P ⟨z, hz⟩ ∈ θ.range)
        ?_ ?_ ?_ ?_ ?_ ?_ hrL
      · rintro z (⟨s, rfl⟩ | hz)
        · obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective s
          have : (⟨ι (mkS G), hSR _⟩ : R) = ψ G := rfl
          rw [this, show Ideal.Quotient.mk P (ψ G) = Ideal.Quotient.mk P (ψ (C (constantCoeff G))) from
            (Ideal.Quotient.eq).mpr (hcong G), ← halgR]
          exact θ.range.algebraMap_mem _
        · rcases hz with rfl | rfl
          · show Ideal.Quotient.mk P x₀R ∈ θ.range
            rw [hθcx]; exact ⟨_, rfl⟩
          · show Ideal.Quotient.mk P x₁R ∈ θ.range
            rw [hθcy]; exact ⟨_, rfl⟩
      · show Ideal.Quotient.mk P ⟨0, _⟩ ∈ θ.range
        rw [show (⟨(0 : L), Subring.zero_mem R⟩ : R) = 0 from rfl, map_zero]; exact zero_mem _
      · show Ideal.Quotient.mk P ⟨1, _⟩ ∈ θ.range
        rw [show (⟨(1 : L), Subring.one_mem R⟩ : R) = 1 from rfl, map_one]; exact one_mem _
      · intro a b ha hb iha ihb
        show Ideal.Quotient.mk P ⟨a + b, _⟩ ∈ θ.range
        rw [show (⟨a + b, Subring.add_mem R ha hb⟩ : R) = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, map_add]
        exact add_mem iha ihb
      · intro a ha iha
        show Ideal.Quotient.mk P ⟨-a, _⟩ ∈ θ.range
        rw [show (⟨-a, Subring.neg_mem R ha⟩ : R) = -⟨a, ha⟩ from rfl, map_neg]
        exact neg_mem iha
      · intro a b ha hb iha ihb
        show Ideal.Quotient.mk P ⟨a * b, _⟩ ∈ θ.range
        rw [show (⟨a * b, Subring.mul_mem R ha hb⟩ : R) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
        exact mul_mem iha ihb
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨w, hw⟩ := hrange r
    exact ⟨w, hw⟩

  let εbar : κ := residue O ε
  have hεbar : εbar = residue O ε := rfl
  have hεbar0 : εbar ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit ε).mpr εu.isUnit
  let u0 : O := constantCoeff pr.u
  have hu0def : u0 = constantCoeff pr.u := rfl
  let v0 : O := constantCoeff pr.v
  have hv0def : v0 = constantCoeff pr.v := rfl
  let ρbar : MvPolynomial (Fin 2) κ :=
    MvPolynomial.C (εbar ^ (q + 1) * residue O v0) - MvPolynomial.C (residue O u0) * drinfeldPoly q κ
  have hρbardef : ρbar =
    MvPolynomial.C (εbar ^ (q + 1) * residue O v0) - MvPolynomial.C (residue O u0) * drinfeldPoly q κ := rfl
  have hcoeff_ρbar : ∀ e : Fin 2 →₀ ℕ, MvPolynomial.coeff e ρbar =
      (if e = 0 then εbar ^ (q + 1) * residue O v0 else 0) -
        residue O u0 * ((if dm1 q = e then 1 else 0) - (if dm2 q = e then 1 else 0)) := by
    intro e
    rw [hρbardef, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, MvPolynomial.coeff_C_mul, coeff_drinfeldPoly]
    by_cases he : e = 0
    · rw [if_pos he, if_pos he.symm]
    · rw [if_neg he, if_neg (Ne.symm he)]
  have hρbar0 : ρbar ≠ 0 := by
    intro h0
    have := hcoeff_ρbar 0
    rw [h0, MvPolynomial.coeff_zero, if_pos rfl, if_neg, if_neg, sub_zero, mul_zero, sub_zero] at this
    · have hv0u : residue O v0 ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hv0
      exact (mul_ne_zero (pow_ne_zero _ hεbar0) hv0u) this.symm
    · intro h; have := congrArg Finsupp.degree h; rw [degree_dm2, map_zero] at this; omega
    · intro h; have := congrArg Finsupp.degree h; rw [degree_dm1, map_zero] at this; omega
  have hπbar : residue O π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr (by change π ∈ 𝔪; rw [hπ]; exact Ideal.mem_span_singleton_self π)
  have hπres : ∀ k : ℕ, 1 ≤ k → residue O (π ^ k) = 0 := by
    intro k hk
    rw [map_pow, hπbar, zero_pow (by omega)]

  have hcoeff_rel : ∀ e : Fin 2 →₀ ℕ, e.degree ≤ q + 1 →
      coeff e pr.rel = π ^ (m * (q + 1)) * (ε ^ (q + 1) * coeff e pr.v) - coeff e (drinfeldForm q O) * u0 := by
    intro e he
    rw [ChartPresentation.rel, map_sub, coeff_C_mul, coeff_f_mul_u pr e he]
    have hpow : ϖ ^ (q + 1) = π ^ (m * (q + 1)) * ε ^ (q + 1) := by rw [hϖε, mul_pow, ← pow_mul]
    rw [hpow]
    ring
  have hρ : ∀ e : Fin 2 →₀ ℕ, m * e.degree ≤ m * (q + 1) →
      ∃ a : O, coeff e pr.rel = π ^ (m * (q + 1) - m * e.degree) * a ∧ residue O a = MvPolynomial.coeff e ρbar := by
    intro e he
    have hdeg : e.degree ≤ q + 1 := Nat.le_of_mul_le_mul_left he (by omega)
    rw [hcoeff_rel e hdeg, hcoeff_ρbar e]
    rcases Nat.lt_or_ge e.degree (q + 1) with hlt | hge
    ·
      refine ⟨π ^ (m * e.degree) * (ε ^ (q + 1) * coeff e pr.v), ?_, ?_⟩
      · rw [coeff_drinfeldForm_eq_zero_of_degree_lt e hlt, zero_mul, sub_zero]
        have hsplit : m * (q + 1) = (m * (q + 1) - m * e.degree) + m * e.degree := (Nat.sub_add_cancel he).symm
        conv_lhs => rw [hsplit, pow_add]
        ring
      · have hd1 : ¬ dm1 q = e := fun h => by rw [← h, degree_dm1] at hlt; omega
        have hd2 : ¬ dm2 q = e := fun h => by rw [← h, degree_dm2] at hlt; omega
        by_cases he0 : e = 0
        · subst he0
          rw [if_pos rfl, if_neg hd1, if_neg hd2, sub_zero, mul_zero, sub_zero, map_zero, mul_zero, pow_zero,
            one_mul, map_mul, map_pow, coeff_zero_eq_constantCoeff_apply]
        · rw [if_neg he0, if_neg hd1, if_neg hd2, sub_zero, mul_zero, sub_zero, map_mul, hπres, zero_mul]
          have : e.degree ≠ 0 := fun h0 => he0 ((Finsupp.degree_eq_zero_iff e).mp h0)
          exact Nat.mul_pos (by omega) (Nat.pos_of_ne_zero this)
    · have hdq : e.degree = q + 1 := le_antisymm hdeg hge
      refine ⟨π ^ (m * (q + 1)) * (ε ^ (q + 1) * coeff e pr.v) - coeff e (drinfeldForm q O) * u0, ?_, ?_⟩
      · rw [hdq, Nat.sub_self, pow_zero, one_mul]
      · have he0 : e ≠ 0 := by
          intro h0; rw [h0, map_zero] at hdq; omega
        rw [if_neg he0, zero_sub, map_sub, map_mul, hπres _ (by nlinarith), zero_mul, zero_sub, map_mul,
          coeff_drinfeldForm, map_sub]
        simp only [apply_ite (residue O), map_one, map_zero]
        ring
  have hρ' : ∀ e : Fin 2 →₀ ℕ, m * (q + 1) < m * e.degree → MvPolynomial.coeff e ρbar = 0 := by
    intro e he
    have hdeg : q + 1 < e.degree := Nat.lt_of_mul_lt_mul_left he
    rw [hcoeff_ρbar, if_neg, if_neg, if_neg, sub_zero, mul_zero, sub_zero]
    · intro h; rw [← h, degree_dm2] at hdeg; omega
    · intro h; rw [← h, degree_dm1] at hdeg; omega
    · intro h; rw [h, map_zero] at hdeg; omega
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := DrinfeldCurve.mk_surjective q κ z
    rw [hθmk] at hz

    let sc : MvPolynomial (Fin 2) κ →ₐ[κ] MvPolynomial (Fin 2) κ :=
      MvPolynomial.aeval (fun i => MvPolynomial.C c⁻¹ * MvPolynomial.X i)
    have hscdef : sc =
      MvPolynomial.aeval (fun i => MvPolynomial.C c⁻¹ * MvPolynomial.X i) := rfl
    let p₁ : MvPolynomial (Fin 2) κ := sc p
    have hp₁def : p₁ = sc p := rfl
    let xbar : Fin 2 → R ⧸ P := ![Ideal.Quotient.mk P x₀R, Ideal.Quotient.mk P x₁R]
    have hxbar : xbar = ![Ideal.Quotient.mk P x₀R, Ideal.Quotient.mk P x₁R] := rfl
    have hxb_xbar : ∀ i, xb i = algebraMap κ (R ⧸ P) c⁻¹ * xbar i := by
      intro i; fin_cases i <;> rfl
    have hp₁ : MvPolynomial.aeval xbar p₁ = 0 := by
      have hcomp : (MvPolynomial.aeval xbar).comp sc = MvPolynomial.aeval xb := by
        rw [hscdef, MvPolynomial.comp_aeval]
        congr 1
        funext i
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hxb_xbar]
      have := congrArg (fun φ => φ p) hcomp
      simp only [AlgHom.comp_apply] at this
      rw [hp₁def, this, hz]

    obtain ⟨P₀, hP₀⟩ := MvPolynomial.map_surjective (residue O) IsLocalRing.residue_surjective p₁
    let xR : Fin 2 → R := ![x₀R, x₁R]
    have hxRdef : xR = ![x₀R, x₁R] := rfl
    let evR : MvPolynomial (Fin 2) O →+* R := MvPolynomial.eval₂Hom (ψ.comp (C : O →+* _)) xR
    have hevRdef : evR = MvPolynomial.eval₂Hom (ψ.comp (C : O →+* _)) xR := rfl
    have hcommev : (Ideal.Quotient.mk P).comp evR =
        (MvPolynomial.eval₂Hom (algebraMap κ (R ⧸ P)) xbar).comp (MvPolynomial.map (residue O)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, hevRdef, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.map_C]
        exact (halgR a).symm
      · intro i
        simp only [RingHom.comp_apply, hevRdef, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.map_X]
        fin_cases i <;> rfl
    have hevP : evR P₀ ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := congrArg (fun φ => φ P₀) hcommev
      simp only [RingHom.comp_apply] at this
      rw [this, hP₀, MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def]
      exact hp₁
    rw [hPdef, Ideal.mem_span_singleton'] at hevP
    obtain ⟨r, hr⟩ := hevP
    obtain ⟨N, B, hB, hrB⟩ := hRform r r.2

    let e := P₀.totalDegree
    have hedef : e = P₀.totalDegree := rfl
    let Apoly : MvPolynomial (Fin 2) O :=
      ∑ α ∈ P₀.support, MvPolynomial.monomial α (MvPolynomial.coeff α P₀ * ϖ ^ (e - α.degree))
    have hApoly : Apoly =
      ∑ α ∈ P₀.support, MvPolynomial.monomial α (MvPolynomial.coeff α P₀ * ϖ ^ (e - α.degree)) := rfl
    have hcoeffP₀ : ∀ α : Fin 2 →₀ ℕ, e < α.degree → MvPolynomial.coeff α P₀ = 0 := by
      intro α hα
      exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt hα
    have hcoeffA : ∀ α, MvPolynomial.coeff α Apoly = MvPolynomial.coeff α P₀ * ϖ ^ (e - α.degree) := by
      intro α
      rw [hApoly, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      by_cases hα : α ∈ P₀.support
      · rw [Finset.sum_eq_single α]
        · rw [if_pos rfl]
        · intro b _ hb; rw [if_neg hb]
        · intro h; exact absurd hα h
      · rw [Finset.sum_eq_zero]
        · rw [MvPolynomial.notMem_support_iff.mp hα, zero_mul]
        · intro b hb; rw [if_neg]; rintro rfl; exact hα hb
    let A : MvPowerSeries (Fin 2) O := (Apoly : MvPowerSeries (Fin 2) O)
    have hAdef : A = (Apoly : MvPowerSeries (Fin 2) O) := rfl
    have hcoeffA' : ∀ α, coeff α A = MvPolynomial.coeff α P₀ * ϖ ^ (e - α.degree) := by
      intro α; rw [hAdef, MvPolynomial.coeff_coe, hcoeffA]

    have hψcoe : ψ.comp (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin 2) O →+* _) =
        MvPolynomial.eval₂Hom (ψ.comp (C : O →+* _)) (fun i => ψ (X i)) := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]
      · intro i; simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]
    have hψXi : ∀ i, ψ (X i) = ϖR * xR i := by
      intro i; fin_cases i
      · exact hψX0
      · exact hψX1
    have hψA : ψ A = ϖR ^ e * evR P₀ := by
      have h1 : ψ A = MvPolynomial.eval₂ (ψ.comp (C : O →+* _)) (fun i => ψ (X i)) Apoly := by
        have := RingHom.congr_fun hψcoe Apoly
        rw [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_eval₂Hom] at this
        exact this
      rw [h1, hApoly, MvPolynomial.eval₂_sum, hevRdef, MvPolynomial.coe_eval₂Hom]
      conv_rhs => rw [MvPolynomial.as_sum P₀, MvPolynomial.eval₂_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
      simp only [RingHom.comp_apply, map_mul, map_pow]
      have hprod : (α.prod fun n k => ψ (X n) ^ k) = ϖR ^ α.degree * α.prod fun n k => xR n ^ k := by
        rw [Finsupp.prod_pow, Finsupp.prod_pow, Fin.prod_univ_two, Fin.prod_univ_two, hψXi 0, hψXi 1,
          Finsupp.degree_eq_sum, Fin.sum_univ_two, mul_pow, mul_pow, pow_add]
        ring
      have hαe : α.degree ≤ e := MvPolynomial.le_totalDegree hα
      rw [hprod, ← map_pow ψ, show ψ (C ϖ ^ (e - α.degree)) = ϖR ^ (e - α.degree) by rw [map_pow]]
      have : ϖR ^ (e - α.degree) * ϖR ^ α.degree = ϖR ^ e := by rw [← pow_add, Nat.sub_add_cancel hαe]
      calc ψ (C (MvPolynomial.coeff α P₀)) * ϖR ^ (e - α.degree) * (ϖR ^ α.degree * α.prod fun n k => xR n ^ k)
          = (ϖR ^ (e - α.degree) * ϖR ^ α.degree) * (ψ (C (MvPolynomial.coeff α P₀)) * α.prod fun n k => xR n ^ k) := by ring
        _ = _ := by rw [this]

    have hidL : ι (mkS (A * C (ϖ ^ N))) = ι (mkS (C (ϖ ^ e) * C π * B)) := by
      have hAL : ι (mkS A) = ϖL ^ e * (ι (mkS (C π)) * (r : L)) := by
        have h := congrArg Subtype.val hψA
        rw [hψ_coe] at h
        rw [h]
        have hr' := congrArg Subtype.val hr
        push_cast at hr' ⊢
        rw [← hr']
        show ϖL ^ e * ((r : L) * ι (mkS (C π))) = ϖL ^ e * (ι (mkS (C π)) * (r : L))
        ring
      simp only [map_mul, map_pow]
      rw [hAL, ← hrB]
      show ϖL ^ e * (ι (mkS (C π)) * ↑r) * ι (mkS (C ϖ)) ^ N = ι (mkS (C ϖ)) ^ e * ι (mkS (C π)) * (↑r * ϖL ^ N)
      rw [hϖLdef, hϖSdef]; ring
    have hidS := hιinj hidL
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hidS
    obtain ⟨H, hH⟩ := hidS

    have hAF : A ∈ F 𝔪 m (m * e) := by
      intro α
      rw [hcoeffA']
      rcases Nat.lt_or_ge e α.degree with hlt | hge
      · rw [hcoeffP₀ α hlt, zero_mul]; exact Ideal.zero_mem _
      · have := hϖpow_mem (e - α.degree)
        rw [Nat.mul_sub] at this
        exact Ideal.mul_mem_left _ _ this
    obtain ⟨cW, hcW⟩ : ∃ cW : ℕ, cW = m * e + m * N := ⟨_, rfl⟩
    have hHF : H * pr.rel ∈ F 𝔪 m cW := by
      rw [hH, hcW]
      refine Ideal.sub_mem _ (mul_mem_F hAF (C_mem_F (m := m) (hϖpow_mem N))) ?_
      have h1 : (C (ϖ ^ e) : MvPowerSeries (Fin 2) O) ∈ F 𝔪 m (m * e) := C_mem_F (hϖpow_mem e)
      have h2 : C π * B ∈ F 𝔪 m (m * N) := Ideal.mul_mem_left _ _ hB
      have := mul_mem_F h1 h2
      rwa [← mul_assoc] at this

    obtain ⟨Q, hQ1, hQ2⟩ :=
      MvPowerSeries.exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
        (Fin 2) O π hπirr m hm (m * (q + 1)) cW pr.rel H ρbar hρbar0 hρ hρ' (fun α => hHF α)

    let Ptil : MvPolynomial (Fin 2) κ :=
      ∑ α ∈ P₀.support, MvPolynomial.monomial α (εbar ^ (e - α.degree + N) * residue O (MvPolynomial.coeff α P₀))

    have hPtil : Ptil =
      ∑ α ∈ P₀.support, MvPolynomial.monomial α (εbar ^ (e - α.degree + N) * residue O (MvPolynomial.coeff α P₀))
      := rfl
    have hcoeffPtil : ∀ α, MvPolynomial.coeff α Ptil =
        εbar ^ (e - α.degree + N) * residue O (MvPolynomial.coeff α P₀) := by
      intro α
      rw [hPtil, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      by_cases hα : α ∈ P₀.support
      · rw [Finset.sum_eq_single α]
        · rw [if_pos rfl]
        · intro b _ hb; rw [if_neg hb]
        · intro h; exact absurd hα h
      · rw [Finset.sum_eq_zero]
        · rw [MvPolynomial.notMem_support_iff.mp hα, map_zero, mul_zero]
        · intro b hb; rw [if_neg]; rintro rfl; exact hα hb
    have hQP : Q * ρbar = Ptil := by
      ext α
      rw [hcoeffPtil]
      rcases Nat.lt_or_ge cW (m * α.degree) with hlt | hge
      · rw [hQ2 α hlt, hcoeffP₀ α, map_zero, mul_zero]
        rw [hcW] at hlt
        have : m * e < m * α.degree := by
          generalize m * e = y at hlt ⊢; generalize m * N = w at hlt; omega
        exact Nat.lt_of_mul_lt_mul_left this
      · obtain ⟨a, ha, hres⟩ := hQ1 α hge
        rw [← hres]

        obtain ⟨k, hk⟩ : ∃ k : ℕ, k = cW - m * α.degree := ⟨_, rfl⟩
        rw [← hk] at ha
        obtain ⟨b, hb⟩ : ∃ b : O, coeff α B = π ^ (m * N - m * α.degree) * b := by
          have h := hB α
          rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
          obtain ⟨b, hb⟩ := h
          exact ⟨b, by rw [← hb, mul_comm]⟩
        let a₁ : O := ε ^ (e - α.degree + N) * MvPolynomial.coeff α P₀
        have ha₁ : a₁ = ε ^ (e - α.degree + N) * MvPolynomial.coeff α P₀ := rfl
        obtain ⟨t, ht⟩ : ∃ t : ℕ, t = m * e + 1 + (m * N - m * α.degree) - k := ⟨_, rfl⟩
        have ht1 : 1 ≤ t := by
          have hge2 := hge
          rw [hcW] at hge2
          have hk2 := hk; rw [hcW] at hk2
          have ht2 := ht
          generalize m * α.degree = z at hge2 hk2 ht2
          generalize m * N = w at hge2 hk2 ht2
          generalize m * e = y at hge2 hk2 ht2
          omega
        let a₂ : O := π ^ t * (ε ^ e * b)
        have ha₂ : a₂ = π ^ t * (ε ^ e * b) := rfl
        have hA1 : coeff α (A * C (ϖ ^ N)) = π ^ k * a₁ := by
          rw [coeff_mul_C, hcoeffA', ha₁]
          rcases Nat.lt_or_ge e α.degree with hlt' | hge'
          · rw [hcoeffP₀ α hlt', zero_mul, zero_mul, mul_zero, mul_zero]
          · rw [mul_assoc, ← pow_add, hϖε, mul_pow, ← pow_mul]
            have : m * (e - α.degree + N) = k := by
              have hmle : m * α.degree ≤ m * e := Nat.mul_le_mul_left m hge'
              rw [Nat.mul_add, Nat.mul_sub, hk, hcW]
              generalize m * α.degree = z at hmle ⊢
              generalize m * N = w
              generalize m * e = y at hmle ⊢
              omega
            rw [this]; ring
        have hA2 : coeff α (C (ϖ ^ e) * C π * B) = π ^ k * a₂ := by
          rw [mul_assoc, coeff_C_mul, coeff_C_mul, hb, hϖε, mul_pow, ← pow_mul, ha₂]
          have : m * e + (1 + (m * N - m * α.degree)) = k + t := by
            have hge2 := hge; rw [hcW] at hge2
            have hk2 := hk; rw [hcW] at hk2
            have ht2 := ht
            generalize m * α.degree = z at hge2 hk2 ht2 ⊢
            generalize m * N = w at hge2 hk2 ht2 ⊢
            generalize m * e = y at hge2 hk2 ht2 ⊢
            omega
          calc π ^ (m * e) * ε ^ e * (π * (π ^ (m * N - m * α.degree) * b))
              = π ^ (m * e + (1 + (m * N - m * α.degree))) * (ε ^ e * b) := by rw [pow_add, pow_add, pow_one]; ring
            _ = π ^ k * (π ^ t * (ε ^ e * b)) := by rw [this, pow_add]; ring
        have hHα : coeff α (H * pr.rel) = π ^ k * (a₁ - a₂) := by
          rw [hH, map_sub, hA1, hA2]; ring
        have haeq : a = a₁ - a₂ := by
          have h1 : π ^ k * a = π ^ k * (a₁ - a₂) := by rw [← ha, hHα]
          exact mul_left_cancel₀ (pow_ne_zero k hπ0) h1
        rw [haeq, map_sub]
        have h2 : residue O a₂ = 0 := by rw [ha₂, map_mul, hπres t ht1, zero_mul]
        rw [h2, sub_zero, ha₁, map_mul, map_pow]

    let scε : MvPolynomial (Fin 2) κ →ₐ[κ] MvPolynomial (Fin 2) κ :=
      MvPolynomial.aeval (fun i => MvPolynomial.C εbar * MvPolynomial.X i)
    have hscε : scε =
      MvPolynomial.aeval (fun i => MvPolynomial.C εbar * MvPolynomial.X i) := rfl
    have hscε_mono : ∀ (α : Fin 2 →₀ ℕ) (a : κ),
        scε (MvPolynomial.monomial α a) = MvPolynomial.monomial α (a * εbar ^ α.degree) := by
      intro α a
      rw [hscε, MvPolynomial.aeval_monomial, Finsupp.prod_pow, Fin.prod_univ_two, Finsupp.degree_eq_sum,
        Fin.sum_univ_two, mul_pow, mul_pow, MvPolynomial.monomial_eq, Finsupp.prod_pow, Fin.prod_univ_two,
        ← MvPolynomial.C_pow, ← MvPolynomial.C_pow, pow_add, MvPolynomial.C_mul, MvPolynomial.C_mul]
      simp only [MvPolynomial.algebraMap_eq]
      ring
    have hscεP : scε Ptil = MvPolynomial.C (εbar ^ (e + N)) * p₁ := by
      rw [hPtil, map_sum, ← hP₀]
      conv_rhs => rw [MvPolynomial.as_sum P₀, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [MvPolynomial.map_monomial]
      have hαe : α.degree ≤ e := MvPolynomial.le_totalDegree hα
      rw [hscε_mono, MvPolynomial.C_mul_monomial]
      congr 1
      have hsum : e - α.degree + N + α.degree = e + N := by omega
      calc εbar ^ (e - α.degree + N) * residue O (MvPolynomial.coeff α P₀) * εbar ^ α.degree
          = residue O (MvPolynomial.coeff α P₀) * εbar ^ (e - α.degree + N + α.degree) := by rw [pow_add]; ring
        _ = _ := by rw [hsum, mul_comm]
    have hscεdP : scε (drinfeldPoly q κ) = MvPolynomial.C (εbar ^ (q + 1)) * drinfeldPoly q κ := by
      rw [hscε, drinfeldPoly]
      simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, map_pow MvPolynomial.C]
      ring
    have hscερ : scε ρbar = MvPolynomial.C (εbar ^ (q + 1)) *
        (MvPolynomial.C (residue O v0) - MvPolynomial.C (residue O u0) * drinfeldPoly q κ) := by
      have hd := hscεdP
      rw [hρbardef]
      simp only [map_sub, map_mul]
      rw [hd]
      simp only [hscε, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul]
      ring
    have hp₁mem : p₁ ∈ Ideal.span {MvPolynomial.C (residue O v0) - MvPolynomial.C (residue O u0) * drinfeldPoly q κ} := by
      have h := congrArg scε hQP
      rw [map_mul, hscερ, hscεP] at h

      have hunit : IsUnit (MvPolynomial.C (εbar ^ (e + N)) : MvPolynomial (Fin 2) κ) :=
        IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hεbar0))
      obtain ⟨w, hw⟩ := hunit
      rw [Ideal.mem_span_singleton']
      refine ⟨((w⁻¹ : (MvPolynomial (Fin 2) κ)ˣ) : MvPolynomial (Fin 2) κ) * scε Q * MvPolynomial.C (εbar ^ (q + 1)), ?_⟩
      have hp : p₁ = ((w⁻¹ : (MvPolynomial (Fin 2) κ)ˣ) : MvPolynomial (Fin 2) κ) * (MvPolynomial.C (εbar ^ (e + N)) * p₁) := by
        rw [← hw, ← mul_assoc, Units.inv_mul, one_mul]
      rw [hp, ← h]; ring

    let scc : MvPolynomial (Fin 2) κ →ₐ[κ] MvPolynomial (Fin 2) κ :=
      MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i)
    have hsccp : scc p₁ = p := by
      have hcomp : scc.comp sc = AlgHom.id κ _ := by
        rw [MvPolynomial.comp_aeval, ← MvPolynomial.aeval_X_left]
        congr 1
        funext i
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, ← mul_assoc,
          ← MvPolynomial.C_mul, inv_mul_cancel₀ hc0, MvPolynomial.C_1, one_mul]
      have := congrArg (fun φ => φ p) hcomp
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at this
      exact this
    have hsccdP : scc (drinfeldPoly q κ) = MvPolynomial.C (c ^ (q + 1)) * drinfeldPoly q κ := by
      simp only [scc, drinfeldPoly, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, map_pow MvPolynomial.C]
      ring
    have hpmem : p ∈ drinfeldIdeal q κ := by
      rw [Ideal.mem_span_singleton'] at hp₁mem
      obtain ⟨t, ht⟩ := hp₁mem
      have h := congrArg scc ht
      rw [hsccp, map_mul, map_sub, map_mul, hsccdP] at h
      simp only [scc, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq] at h
      have hcv : MvPolynomial.C (residue O u0) * (MvPolynomial.C (c ^ (q + 1)) * drinfeldPoly q κ) =
          MvPolynomial.C (residue O v0) * drinfeldPoly q κ := by
        rw [← mul_assoc, ← MvPolynomial.C_mul, mul_comm (residue O u0), hcrel]
      rw [hcv] at h
      rw [drinfeldIdeal, Ideal.mem_span_singleton']
      refine ⟨-(MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i) t * MvPolynomial.C (residue O v0)), ?_⟩
      rw [← h]; ring
    show Ideal.Quotient.mkₐ κ (drinfeldIdeal q κ) p = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hpmem

  let eθ : CR ≃ₐ[κ] R ⧸ P := AlgEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  haveI : IsDomain (R ⧸ P) :=
    Function.Injective.isDomain (eθ.symm : (R ⧸ P) →+* CR) eθ.symm.injective
  have hPprime : P.IsPrime := (Ideal.Quotient.isDomain_iff_prime P).mp inferInstance
  let eR : (R ⧸ P) ≃ₐ[κ] CR := eθ.symm
  have heR0 : eR (Ideal.Quotient.mk P ⟨x₀, hx₀⟩) = algebraMap κ CR c * x q κ := by
    show eθ.symm (Ideal.Quotient.mk P x₀R) = _
    rw [AlgEquiv.symm_apply_eq, hθcx]
    exact (AlgEquiv.ofBijective_apply _ _ _).symm
  have heR1 : eR (Ideal.Quotient.mk P ⟨x₁, hx₁⟩) = algebraMap κ CR c * y q κ := by
    show eθ.symm (Ideal.Quotient.mk P x₁R) = _
    rw [AlgEquiv.symm_apply_eq, hθcy]
    exact (AlgEquiv.ofBijective_apply _ _ _).symm

  have hnoeth : IsNoetherianRing R := by
    haveI : IsNoetherianRing (MvPowerSeries (Fin 2) O) := MvPowerSeries.isNoetherianRing_of_finite
    haveI hSno : IsNoetherianRing pr.Ring := Ideal.Quotient.isNoetherianRing _
    let f : MvPolynomial (Fin 2) pr.Ring →+* L := MvPolynomial.eval₂Hom ι ![x₀, x₁]
    have hfmem : ∀ pp : MvPolynomial (Fin 2) pr.Ring, f pp ∈ R := by
      intro pp
      induction pp using MvPolynomial.induction_on with
      | C a => rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; exact hSR a
      | add p₁ p₂ ih₁ ih₂ => rw [map_add]; exact Subring.add_mem _ ih₁ ih₂
      | mul_X pp i ih =>
        rw [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        refine Subring.mul_mem _ ih ?_
        fin_cases i
        · exact hx₀
        · exact hx₁
    let fR : MvPolynomial (Fin 2) pr.Ring →+* R := f.codRestrict R hfmem
    have hfR : Function.Surjective fR := by
      rintro ⟨z, hz⟩
      refine Subring.closure_induction (p := fun z hz => ∃ pp, fR pp = ⟨z, hz⟩) ?_ ?_ ?_ ?_ ?_ ?_ hz
      · rintro w (⟨s, rfl⟩ | hw)
        · exact ⟨MvPolynomial.C s, Subtype.ext (by
            show f (MvPolynomial.C s) = ι s
            rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C])⟩
        · rcases hw with rfl | rfl
          · exact ⟨MvPolynomial.X 0, Subtype.ext (by
              show f (MvPolynomial.X 0) = x₀
              rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl)⟩
          · exact ⟨MvPolynomial.X 1, Subtype.ext (by
              show f (MvPolynomial.X 1) = x₁
              rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl)⟩
      · exact ⟨0, by rw [map_zero]; rfl⟩
      · exact ⟨1, by rw [map_one]; rfl⟩
      · rintro a b ha hb ⟨pa, hpa⟩ ⟨pb, hpb⟩
        exact ⟨pa + pb, by rw [map_add, hpa, hpb]; rfl⟩
      · rintro a ha ⟨pa, hpa⟩
        exact ⟨-pa, by rw [map_neg, hpa]; rfl⟩
      · rintro a b ha hb ⟨pa, hpa⟩ ⟨pb, hpb⟩
        exact ⟨pa * pb, by rw [map_mul, hpa, hpb]; rfl⟩
    exact isNoetherianRing_of_surjective _ _ fR hfR
  exact ⟨hι₀, hx₀, hx₁, P, rfl, hnoeth, hPprime, algR, halgR', eR, c, hcen, hc0, hcrel, heR0, heR1⟩

end Main

end BlowupFibreSol

end

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (GaloisField q 2) (ResidueField O)]
    [IsAlgClosed (ResidueField O)] [IsDomain (CoordRing q (ResidueField O))]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (pr : ChartPresentation q O ϖ)
    (hnzd : Ideal.Quotient.mk (Ideal.span {pr.rel}) (C ϖ) ∈ nonZeroDivisors pr.Ring) :
    let S := pr.Ring
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk _
    let L := Localization.Away (mkS (C ϖ))
    let ι₀ : O →+* L := (algebraMap S L).comp (mkS.comp (C (σ := Fin 2) (R := O)))
    let x₀ : L := algebraMap S L (mkS (X 0)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let x₁ : L := algebraMap S L (mkS (X 1)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let R : Subring L := Subring.closure (Set.range (algebraMap S L) ∪ {x₀, x₁})
    ∃ (hι₀ : ∀ o : O, ι₀ o ∈ R) (hx₀ : x₀ ∈ R) (hx₁ : x₁ ∈ R)
      (P : Ideal ↥R) (_ : P = Ideal.span {(⟨ι₀ π, hι₀ π⟩ : ↥R)})
      (_ : IsNoetherianRing ↥R) (hP : P.IsPrime)
      (algR : Algebra (ResidueField O) (↥R ⧸ P))
      (_ : ∀ a : O, algebraMap (ResidueField O) (↥R ⧸ P) (residue O a) = Ideal.Quotient.mk P ⟨ι₀ a, hι₀ a⟩)
      (eR : (↥R ⧸ P) ≃ₐ[ResidueField O] CoordRing q (ResidueField O))
      (c : ResidueField O),

      (∀ s : S, (∃ a ∈ maximalIdeal O, ∃ g₀ g₁ : MvPowerSeries (Fin 2) O, s = mkS (C a + X 0 * g₀ + X 1 * g₁)) →
        ∃ h : algebraMap S L s ∈ R, (⟨_, h⟩ : ↥R) ∈ P) ∧

      c ≠ 0 ∧
      c ^ (q + 1) * residue O (MvPowerSeries.constantCoeff pr.u) = residue O (MvPowerSeries.constantCoeff pr.v) ∧
      eR (Ideal.Quotient.mk P ⟨x₀, hx₀⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * x q (ResidueField O) ∧
      eR (Ideal.Quotient.mk P ⟨x₁, hx₁⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * y q (ResidueField O) :=
  BlowupFibreSol.main q O π hπ ϖ hϖ hϖ0 pr hnzd

end S_DrinfeldCurve_LocalChart_exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal (solution)
