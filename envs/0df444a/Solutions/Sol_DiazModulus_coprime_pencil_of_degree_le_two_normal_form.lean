-- Prove2me | solution 1 for DiazModulus.coprime_pencil_of_degree_le_two_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:26.917596+00:00
-- url     : https://prove2.me/submissions/daed827a-588f-4f57-a831-fc11d50a2d15

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A coprime pencil of degree at most two has one of four normal forms

Let `P = span(a₀, a₁)` with `a₀, a₁` coprime, of degrees at most two, not both constant.
Coprimality makes `a₀, a₁` linearly independent, so `dim P = 2`.
If both have no `X²` term, `P` lies in `span(1, X)` and equals it by dimension.
Otherwise `P` contains a monic `f = X² + dX + e`, and the element `r = x₂a₁ − y₂a₀`
(`x₂, y₂` the `X²` coefficients) is non-zero of degree at most one.
If `r` is a constant, `1 ∈ P` and `P = span(1, X² + dX)`.
Otherwise `X + β ∈ P`. For `β = 0`, `P = span(X, X² + e)`, and `e ≠ 0` since `X` is not a common factor.
For `β ≠ 0`, `P = span(X + β, X² + γX)` with `γ = d − e/β`, and `γ ≠ β` since `X + β` is not a
common factor. Each span equality holds because two polynomials of distinct degrees in `P`
span a plane inside the plane `P`.
-/

open Polynomial

namespace R18_L1

open DiazModulus

variable {K : Type*} [Field K]

/-- Two polynomials of distinct degrees, the lower one non-zero, span a plane. -/
theorem finrank_pair {p q : K[X]} (hp : p ≠ 0) (hpq : p.natDegree < q.natDegree) :
    Module.finrank K (Submodule.span K ({p, q} : Set K[X])) = 2 := by
  have hq : q ≠ 0 := by rintro rfl; simp at hpq
  have hli : LinearIndependent K ![p, q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have := congrArg (fun f => f.coeff q.natDegree) hst
      simpa [coeff_eq_zero_of_natDegree_lt hpq, hq] using this
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hp, rfl⟩
  have := finrank_span_eq_card hli
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this

/-- Two such polynomials in a subspace of dimension at most two span it. -/
theorem span_eq {P : Submodule K K[X]} [FiniteDimensional K P] (hP : Module.finrank K P ≤ 2)
    {p q : K[X]} (hp : p ≠ 0) (hpq : p.natDegree < q.natDegree) (hpP : p ∈ P) (hqP : q ∈ P) :
    P = Submodule.span K ({p, q} : Set K[X]) := by
  symm
  refine Submodule.eq_of_le_of_finrank_le ?_ (by rw [finrank_pair hp hpq]; exact hP)
  rw [Submodule.span_le]
  intro f hf
  rcases hf with rfl | rfl
  · exact hpP
  · exact hqP

theorem dvd_of_mem_pair {g p q f : K[X]} (hp : g ∣ p) (hq : g ∣ q)
    (hf : f ∈ Submodule.span K ({p, q} : Set K[X])) : g ∣ f := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hf
  rw [smul_eq_C_mul, smul_eq_C_mul]
  exact dvd_add (dvd_mul_of_dvd_right hp _) (dvd_mul_of_dvd_right hq _)

theorem quad_eq {f : K[X]} (h : f.natDegree ≤ 2) :
    f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem deg_le_one {f : K[X]} (h : f.natDegree ≤ 2) (h2 : f.coeff 2 = 0) : f.natDegree ≤ 1 := by
  by_contra hc
  have hd : f.natDegree = 2 := by omega
  have : f.leadingCoeff = 0 := by rw [leadingCoeff, hd]; exact h2
  rw [leadingCoeff_eq_zero] at this
  subst this
  simp at hd

end R18_L1

open DiazModulus R18_L1 in
open Polynomial in
theorem solution (K : Type*) [Field K] (a₀ a₁ : K[X])
    (hcop : IsCoprime a₀ a₁) (hdeg : 1 ≤ max a₀.natDegree a₁.natDegree)
    (hdeg2 : max a₀.natDegree a₁.natDegree ≤ 2) :
    ∃ p q : K[X], Submodule.span K ({a₀, a₁} : Set K[X]) = Submodule.span K ({p, q} : Set K[X]) ∧
      ((p = 1 ∧ q = X) ∨ (∃ α : K, p = 1 ∧ q = X ^ 2 + C α * X) ∨
        (∃ β : K, β ≠ 0 ∧ p = X ∧ q = X ^ 2 + C β) ∨
        (∃ β γ : K, β ≠ 0 ∧ γ ≠ β ∧ p = X + C β ∧ q = X ^ 2 + C γ * X)) := by
  set P := Submodule.span K ({a₀, a₁} : Set K[X]) with hPdef
  have h0 : a₀.natDegree ≤ 2 := le_trans (le_max_left _ _) hdeg2
  have h1 : a₁.natDegree ≤ 2 := le_trans (le_max_right _ _) hdeg2
  have ha₀ : a₀ ∈ P := Submodule.subset_span (by simp)
  have ha₁ : a₁ ∈ P := Submodule.subset_span (by simp)
  have : FiniteDimensional K P := FiniteDimensional.span_of_finite K (Set.toFinite _)
  -- coprimality: no common factor of positive degree
  have hunit : ∀ {g p q : K[X]}, P = Submodule.span K ({p, q} : Set K[X]) → g ∣ p → g ∣ q →
      IsUnit g := by
    intro g p q hP hp hq
    exact hcop.isUnit_of_dvd' (dvd_of_mem_pair hp hq (hP ▸ ha₀))
      (dvd_of_mem_pair hp hq (hP ▸ ha₁))
  -- linear independence of a₀, a₁
  have hli : LinearIndependent K ![a₀, a₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      refine ⟨?_, rfl⟩
      rcases hst with hs | rfl
      · exact hs
      · have := natDegree_eq_zero_of_isUnit (hcop.isUnit_of_dvd' (dvd_zero a₁) dvd_rfl)
        simp [this] at hdeg
    · exfalso
      have hrel : a₁ = C (-(s / t)) * a₀ := by
        have hct : C t⁻¹ * C t = 1 := by rw [← C_mul, inv_mul_cancel₀ ht, C_1]
        rw [smul_eq_C_mul, smul_eq_C_mul] at hst
        rw [C_neg, div_eq_inv_mul, C_mul]
        linear_combination (C t⁻¹) * hst - a₁ * hct
      have hu := hcop.isUnit_of_dvd' dvd_rfl (hrel ▸ dvd_mul_left a₀ _)
      have hd0 := natDegree_eq_zero_of_isUnit hu
      have hd1 : a₁.natDegree = 0 := by
        rw [hrel]; exact Nat.eq_zero_of_le_zero ((natDegree_C_mul_le _ _).trans hd0.le)
      simp [hd0, hd1] at hdeg
  have hP2 : Module.finrank K P = 2 := by
    have := finrank_span_eq_card hli
    rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
  by_cases h2 : a₀.coeff 2 = 0 ∧ a₁.coeff 2 = 0
  · -- (i): `P ⊆ span(1, X)`
    refine ⟨1, X, ?_, Or.inl ⟨rfl, rfl⟩⟩
    have hmem : ∀ f : K[X], f.natDegree ≤ 1 → f ∈ Submodule.span K ({1, X} : Set K[X]) := by
      intro f hf
      rw [eq_X_add_C_of_natDegree_le_one hf]
      exact Submodule.mem_span_pair.mpr ⟨f.coeff 0, f.coeff 1, by
        rw [smul_eq_C_mul, smul_eq_C_mul, mul_one, add_comm]⟩
    have hle : P ≤ Submodule.span K ({1, X} : Set K[X]) := by
      rw [Submodule.span_le]
      intro f hf
      rcases hf with rfl | rfl
      · exact hmem _ (deg_le_one h0 h2.1)
      · exact hmem _ (deg_le_one h1 h2.2)
    have : FiniteDimensional K (Submodule.span K ({1, X} : Set K[X])) :=
      FiniteDimensional.span_of_finite K (Set.toFinite _)
    exact Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_pair one_ne_zero (by simp), hP2])
  · -- a monic quadratic `X² + dX + e` in `P`
    obtain ⟨d, e, hfP⟩ : ∃ d e : K, X ^ 2 + C d * X + C e ∈ P := by
      have key : ∀ a : K[X], a ∈ P → a.natDegree ≤ 2 → a.coeff 2 ≠ 0 →
          ∃ d e : K, X ^ 2 + C d * X + C e ∈ P := by
        intro a ha hd hc
        refine ⟨(a.coeff 2)⁻¹ * a.coeff 1, (a.coeff 2)⁻¹ * a.coeff 0, ?_⟩
        have : X ^ 2 + C ((a.coeff 2)⁻¹ * a.coeff 1) * X + C ((a.coeff 2)⁻¹ * a.coeff 0)
            = (a.coeff 2)⁻¹ • a := by
          rw [smul_eq_C_mul]
          conv_rhs => arg 2; rw [quad_eq hd]
          rw [C_mul, C_mul]
          have hcc : C (a.coeff 2)⁻¹ * C (a.coeff 2) = 1 := by
            rw [← C_mul, inv_mul_cancel₀ hc, C_1]
          linear_combination (-X ^ 2) * hcc
        rw [this]; exact P.smul_mem _ ha
      by_cases hx : a₀.coeff 2 = 0
      · exact key a₁ ha₁ h1 (fun hy => h2 ⟨hx, hy⟩)
      · exact key a₀ ha₀ h0 hx
    -- a non-zero element of degree at most one
    obtain ⟨c, c₀, hr0, hrP⟩ : ∃ c c₀ : K, (c ≠ 0 ∨ c₀ ≠ 0) ∧ C c * X + C c₀ ∈ P := by
      set r := a₀.coeff 2 • a₁ - a₁.coeff 2 • a₀ with hr
      have hrP : r ∈ P := P.sub_mem (P.smul_mem _ ha₁) (P.smul_mem _ ha₀)
      have hrd : r.natDegree ≤ 2 :=
        (natDegree_sub_le _ _).trans (max_le ((natDegree_smul_le _ _).trans h1)
          ((natDegree_smul_le _ _).trans h0))
      have hr2 : r.coeff 2 = 0 := by simp [hr, mul_comm]
      have hr1 := deg_le_one hrd hr2
      have hrne : r ≠ 0 := by
        intro hr0
        have := (LinearIndependent.pair_iff.mp hli) (-(a₁.coeff 2)) (a₀.coeff 2)
          (by rw [neg_smul, ← hr0, hr]; abel)
        exact h2 ⟨this.2, neg_eq_zero.mp this.1⟩
      refine ⟨r.coeff 1, r.coeff 0, ?_, (eq_X_add_C_of_natDegree_le_one hr1) ▸ hrP⟩
      by_contra hc
      push Not at hc
      apply hrne
      rw [eq_X_add_C_of_natDegree_le_one hr1, hc.1, hc.2]
      simp
    have hP2' : Module.finrank K P ≤ 2 := hP2.le
    by_cases hc : c = 0
    · -- (ii): `1 ∈ P`
      subst hc
      have hc₀ : c₀ ≠ 0 := hr0.resolve_left (fun h => h rfl)
      have h1P : (1 : K[X]) ∈ P := by
        have : (1 : K[X]) = c₀⁻¹ • (C 0 * X + C c₀) := by
          rw [smul_eq_C_mul, C_0, zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hc₀, C_1]
        rw [this]; exact P.smul_mem _ hrP
      have hqP : X ^ 2 + C d * X ∈ P := by
        have : X ^ 2 + C d * X = (X ^ 2 + C d * X + C e) - e • (1 : K[X]) := by
          rw [smul_eq_C_mul, mul_one]; ring
        rw [this]; exact P.sub_mem hfP (P.smul_mem _ h1P)
      refine ⟨1, X ^ 2 + C d * X, span_eq hP2' one_ne_zero ?_ h1P hqP,
        Or.inr (Or.inl ⟨d, rfl, rfl⟩)⟩
      rw [natDegree_one, show (X ^ 2 + C d * X : K[X]).natDegree = 2 by compute_degree!]; norm_num
    · -- `X + β ∈ P`
      have hβP : X + C (c₀ / c) ∈ P := by
        have : X + C (c₀ / c) = c⁻¹ • (C c * X + C c₀) := by
          rw [smul_eq_C_mul, mul_add, ← mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ hc, C_1,
            one_mul, div_eq_inv_mul]
        rw [this]; exact P.smul_mem _ hrP
      set β := c₀ / c with hβdef
      by_cases hβ : β = 0
      · -- (iii): `X ∈ P`
        rw [hβ, C_0, add_zero] at hβP
        have hqP : X ^ 2 + C e ∈ P := by
          have : X ^ 2 + C e = (X ^ 2 + C d * X + C e) - d • X := by
            rw [smul_eq_C_mul]; ring
          rw [this]; exact P.sub_mem hfP (P.smul_mem _ hβP)
        have hPe := span_eq hP2' X_ne_zero (by rw [natDegree_X, natDegree_X_pow_add_C]; norm_num)
          hβP hqP
        refine ⟨X, X ^ 2 + C e, hPe, Or.inr (Or.inr (Or.inl ⟨e, ?_, rfl, rfl⟩))⟩
        rintro rfl
        exact not_isUnit_X (hunit hPe dvd_rfl ⟨X, by rw [C_0, add_zero, sq]⟩)
      · -- (iv): `X + β ∈ P` with `β ≠ 0`
        have hqP : X ^ 2 + C (d - e / β) * X ∈ P := by
          have : X ^ 2 + C (d - e / β) * X = (X ^ 2 + C d * X + C e) - (e / β) • (X + C β) := by
            have hh : C (e / β) * C β = C e := by rw [← C_mul, div_mul_cancel₀ e hβ]
            rw [smul_eq_C_mul, C_sub]
            linear_combination hh
          rw [this]; exact P.sub_mem hfP (P.smul_mem _ hβP)
        have hPe := span_eq hP2' (X_add_C_ne_zero β)
          (by rw [natDegree_X_add_C, show (X ^ 2 + C (d - e / β) * X : K[X]).natDegree = 2 by
            compute_degree!]; norm_num) hβP hqP
        refine ⟨X + C β, X ^ 2 + C (d - e / β) * X, hPe,
          Or.inr (Or.inr (Or.inr ⟨β, d - e / β, hβ, ?_, rfl, rfl⟩))⟩
        intro hγ
        rw [hγ] at hPe
        have := hunit hPe dvd_rfl ⟨X, by ring⟩
        exact not_isUnit_X_add_C β this
