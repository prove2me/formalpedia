-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/89ee169d-2c27-549b-a993-8d5105b01eaa

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace F530

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

theorem frobTwist_frobTwist {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (frobTwist Onr Fr b ψ) = frobTwist Onr Fr (b + a) ψ := by
  apply AlgHom.ext
  intro x
  simp [frobTwist, AlgHom.comp_apply, zpow_add, AlgEquiv.mul_apply]

theorem frobTwist_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr 0 ψ = ψ := by
  apply AlgHom.ext
  intro x
  simp [frobTwist]

theorem frobTwist_comm {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (frobTwist Onr Fr b ψ) = frobTwist Onr Fr b (frobTwist Onr Fr a ψ) := by
  rw [frobTwist_frobTwist, frobTwist_frobTwist, add_comm]

theorem frobTwist_comp {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (a : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (φ.comp ψ) = φ.comp (frobTwist Onr Fr a ψ) := by
  apply AlgHom.ext
  intro x
  simp [frobTwist]

theorem apply_pow_aux {r : ℕ} (π' : Onr) {F : Type} [CommRing F] (φ : Onr →+* F)
    (hφ : ∀ x ∈ Ideal.span ({π'} : Set Onr), φ x = 0)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span ({π'} : Set Onr)) :
    ∀ (k : ℕ) (x : Onr), φ ((Fr ^ k) x) = φ x ^ (r ^ k) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih (Fr x)]
      have h1 : φ (Fr x) = φ x ^ r := by
        have := hφ _ (hFr x)
        rw [map_sub, sub_eq_zero, map_pow] at this
        exact this
      rw [h1, ← pow_mul, pow_succ']

theorem eq_zero_of_frobTwist_eq {r : ℕ} [Fact r.Prime] (π : 𝒪) [Nontrivial Onr]
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {B : Type} [CommRing B] [Algebra 𝒪 B] [Nontrivial B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ψ : Onr →ₐ[𝒪] B) (m : ℤ) (hm : frobTwist Onr Fr m ψ = ψ) : m = 0 := by
  classical

  have key : ∀ k : ℕ, frobTwist Onr Fr (k : ℤ) ψ = ψ → k = 0 := by
    intro k hk
    by_contra hk0
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0

    obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal B
    letI : Field (B ⧸ 𝔫) := Ideal.Quotient.field 𝔫
    set φ : Onr →+* B ⧸ 𝔫 := (Ideal.Quotient.mk 𝔫).comp (ψ : Onr →+* B) with hφdef
    have hφπ : φ (algebraMap 𝒪 Onr π) = 0 := by
      have h1 : (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π := ψ.commutes π
      have h2 : IsNilpotent (φ (algebraMap 𝒪 Onr π)) := by
        rw [hφdef, RingHom.comp_apply, h1]
        exact hB.map _
      exact h2.eq_zero
    have hφI : ∀ x ∈ Ideal.span ({algebraMap 𝒪 Onr π} : Set Onr), φ x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, hφπ, mul_zero]

    have hfix : ∀ x : Onr, φ x ^ (r ^ k) = φ x := by
      intro x
      rw [← apply_pow_aux Fr (algebraMap 𝒪 Onr π) φ hφI hFr k x]
      have := AlgHom.congr_fun hk x
      simp only [frobTwist, AlgHom.comp_apply, zpow_natCast, AlgEquiv.coe_algHom] at this
      rw [hφdef, RingHom.comp_apply, RingHom.comp_apply]
      exact congrArg (Ideal.Quotient.mk 𝔫) this

    set q : ℕ := r ^ k with hq
    have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
    have hq2 : 2 ≤ q := by
      rw [hq]
      calc 2 ≤ r := hr2
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ k := Nat.pow_le_pow_right (by omega) hk1
    have hlt : (Polynomial.X - Polynomial.C (1 : Onr)).natDegree < (Polynomial.X ^ q : Polynomial Onr).natDegree := by
      rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_pow]; omega
    have hmonic : (Polynomial.X ^ q - (Polynomial.X - Polynomial.C (1 : Onr))).Monic :=
      Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow q) (Polynomial.degree_lt_degree hlt)
    have hdeg : 0 < (Polynomial.X ^ q - (Polynomial.X - Polynomial.C (1 : Onr))).natDegree := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]; omega
    obtain ⟨x₀, hx₀⟩ := hOnr_closed _ hmonic hdeg
    have h0 := hφI _ hx₀
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, map_sub, map_pow,
      map_one] at h0
    rw [hfix x₀] at h0
    simp at h0
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · exact_mod_cast key k hm
  · have hk : frobTwist Onr Fr (k : ℤ) ψ = ψ := by
      have := congrArg (frobTwist Onr Fr (k : ℤ)) hm
      rw [frobTwist_frobTwist, neg_add_cancel, frobTwist_zero] at this
      exact this.symm
    have := key k hk
    simp [this]

theorem eq_of_frobTwist_eq_frobTwist {r : ℕ} [Fact r.Prime] (π : 𝒪) [Nontrivial Onr]
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {B : Type} [CommRing B] [Algebra 𝒪 B] [Nontrivial B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ψ : Onr →ₐ[𝒪] B) (a b : ℤ) (h : frobTwist Onr Fr a ψ = frobTwist Onr Fr b ψ) : a = b := by
  have h2 : frobTwist Onr Fr (a - b) ψ = ψ := by
    have := congrArg (frobTwist Onr Fr (-b)) h
    rw [frobTwist_frobTwist, frobTwist_frobTwist, add_neg_cancel, frobTwist_zero] at this
    rw [← sub_eq_add_neg] at this
    exact this
  have := eq_zero_of_frobTwist_eq Fr π hOnr_closed hFr hB ψ (a - b) h2
  omega

end F530

theorem solution
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {r : ℕ} [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [Nontrivial Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Nontrivial B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ψ : Onr →ₐ[𝒪] B) (a b : ℤ) (h : frobTwist Onr Fr a ψ = frobTwist Onr Fr b ψ) : a = b :=
  F530.eq_of_frobTwist_eq_frobTwist Fr π hOnr_closed hFr hB ψ a b h

end S_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial (solution)
