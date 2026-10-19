-- Prove2me | solution 1 for DiazModulus.shifted_polynomial_hull_orders
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:05:00.407978+00:00
-- url     : https://prove2.me/submissions/a7c8e6f1-16f7-4270-9bfb-bb68c431b1f1

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Orders and degrees in a shifted polynomial hull

Let `2 ≤ m ≤ k`, let `Q₁ ≠ 0` have trailing degree `k + m` and degree `2k`, and let `Q₂` have
non-zero constant term and degree `k - m`. A non-zero element of the span of
`X^(k-1), X^k, X^(k+1), Q₁, Q₂` is `f = c₁X^(k-1) + c₂X^k + c₃X^(k+1) + αQ₁ + βQ₂`. Since
`k - 1 ≥ 1`, only `Q₂` contributes to the constant term; `Q₁` is supported in `[k + m, 2k]` with
`k + m ≥ k + 2`, and `Q₂` in `[0, k - m]` with `k - m ≤ k - 2`. Reading off coefficients:

* the trailing degree of `f` is `0` if `β ≠ 0`, otherwise the position of the first non-zero
  among `c₁, c₂, c₃` (at `k - 1, k, k + 1`), and otherwise `k + m` (then `f = αQ₁`, `α ≠ 0`);
* the degree of `f` is `2k` if `α ≠ 0`, otherwise the position of the last non-zero among
  `c₃, c₂, c₁`, and otherwise `k - m` (then `f = βQ₂`, `β ≠ 0`).
-/

namespace R16_shiftOrders

open Polynomial

variable {K : Type*} [Field K]

theorem ntd_eq {f : K[X]} {n : ℕ} (h : f.coeff n ≠ 0) (hlt : ∀ i < n, f.coeff i = 0) :
    f.natTrailingDegree = n :=
  le_antisymm (natTrailingDegree_le_of_ne_zero h)
    (le_natTrailingDegree (fun h0 => h (by rw [h0, coeff_zero])) hlt)

theorem nd_eq {f : K[X]} {n : ℕ} (h : f.coeff n ≠ 0) (hgt : ∀ i, n < i → f.coeff i = 0) :
    f.natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr hgt) h

end R16_shiftOrders

open DiazModulus Polynomial R16_shiftOrders in
theorem solution (K : Type*) [Field K] (k m : ℕ) (hm : 2 ≤ m) (hmk : m ≤ k)
    (Q₁ Q₂ : K[X]) (hQ₁ : Q₁ ≠ 0) (hQ₁t : Q₁.natTrailingDegree = k + m)
    (hQ₁d : Q₁.natDegree = 2 * k) (hQ₂ : Q₂.coeff 0 ≠ 0) (hQ₂d : Q₂.natDegree = k - m)
    (f : K[X]) (hf : f ∈ Submodule.span K ({X ^ (k - 1), X ^ k, X ^ (k + 1), Q₁, Q₂} : Set K[X]))
    (hf0 : f ≠ 0) :
    f.natTrailingDegree ∈ ({0, k - 1, k, k + 1, k + m} : Finset ℕ) ∧
      f.natDegree ∈ ({k - m, k - 1, k, k + 1, 2 * k} : Finset ℕ) := by
  obtain ⟨c₁, f₁, hf₁, e₁⟩ := Submodule.mem_span_insert.mp hf
  obtain ⟨c₂, f₂, hf₂, e₂⟩ := Submodule.mem_span_insert.mp hf₁
  obtain ⟨c₃, f₃, hf₃, e₃⟩ := Submodule.mem_span_insert.mp hf₂
  obtain ⟨α, f₄, hf₄, e₄⟩ := Submodule.mem_span_insert.mp hf₃
  obtain ⟨β, e₅⟩ := Submodule.mem_span_singleton.mp hf₄
  have hQ₂0 : Q₂ ≠ 0 := fun h => hQ₂ (by rw [h, coeff_zero])
  have lo₁ : ∀ i < k + m, Q₁.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  have hi₁ : ∀ i, 2 * k < i → Q₁.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hi₂ : ∀ i, k - m < i → Q₂.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  have t₁ : Q₁.coeff (k + m) ≠ 0 := by
    rw [← hQ₁t]; exact trailingCoeff_nonzero_iff_nonzero.mpr hQ₁
  have d₁ : Q₁.coeff (2 * k) ≠ 0 := by rw [← hQ₁d]; exact leadingCoeff_ne_zero.mpr hQ₁
  have d₂ : Q₂.coeff (k - m) ≠ 0 := by rw [← hQ₂d]; exact leadingCoeff_ne_zero.mpr hQ₂0
  have hc : ∀ i, f.coeff i = (if i = k - 1 then c₁ else 0) + ((if i = k then c₂ else 0) +
      ((if i = k + 1 then c₃ else 0) + (α * Q₁.coeff i + β * Q₂.coeff i))) := by
    intro i
    rw [e₁, e₂, e₃, e₄, ← e₅]
    simp only [coeff_add, coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hlow : ∀ i ≤ k + 1, f.coeff i = (if i = k - 1 then c₁ else 0) +
      ((if i = k then c₂ else 0) + ((if i = k + 1 then c₃ else 0) + β * Q₂.coeff i)) := by
    intro i hi; rw [hc, lo₁ i (by omega), mul_zero, zero_add]
  have hhigh : ∀ i, k - 1 ≤ i → f.coeff i = (if i = k - 1 then c₁ else 0) +
      ((if i = k then c₂ else 0) + ((if i = k + 1 then c₃ else 0) + α * Q₁.coeff i)) := by
    intro i hi; rw [hc, hi₂ i (by omega), mul_zero, add_zero]
  have a₁ : k - 1 ≠ k := by omega
  have a₂ : k - 1 ≠ k + 1 := by omega
  have a₄ : k + 1 ≠ k - 1 := by omega
  have a₅ : 2 * k ≠ k - 1 := by omega
  have a₆ : 2 * k ≠ k := by omega
  have a₇ : 2 * k ≠ k + 1 := by omega
  have a₈ : k ≠ k - 1 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · -- the trailing degree
    by_cases hβ : β = 0
    · subst hβ
      by_cases h₁ : c₁ = 0
      · subst h₁
        by_cases h₂ : c₂ = 0
        · subst h₂
          by_cases h₃ : c₃ = 0
          · subst h₃
            rcases eq_or_ne α 0 with rfl | hα
            · exact absurd (by ext i; rw [hc]; simp) hf0
            right; right; right; right
            refine ntd_eq ?_ fun i hi => ?_
            · rw [hc]; simp [hα, t₁]
            · rw [hc, lo₁ i hi]; simp
          · right; right; right; left
            refine ntd_eq ?_ fun i hi => ?_
            · rw [hlow _ le_rfl]; simp [h₃]
            · rw [hlow i (by omega)]; simp [hi.ne]
        · right; right; left
          refine ntd_eq ?_ fun i hi => ?_
          · rw [hlow _ (by omega)]; simp [h₂]
          · have b₁ : i ≠ k + 1 := by omega
            rw [hlow i (by omega)]; simp [hi.ne, b₁]
      · right; left
        refine ntd_eq ?_ fun i hi => ?_
        · rw [hlow _ (by omega)]; simp [h₁, a₁, a₂]
        · have b₁ : i ≠ k := by omega
          have b₂ : i ≠ k + 1 := by omega
          rw [hlow i (by omega)]; simp [hi.ne, b₁, b₂]
    · left
      refine ntd_eq ?_ fun i hi => absurd hi (Nat.not_lt_zero i)
      have b₁ : (0 : ℕ) ≠ k - 1 := by omega
      have b₂ : (0 : ℕ) ≠ k := by omega
      rw [hlow 0 (by omega)]; simp [b₁, b₂, hβ, hQ₂]
  · -- the degree
    by_cases hα : α = 0
    · subst hα
      by_cases h₃ : c₃ = 0
      · subst h₃
        by_cases h₂ : c₂ = 0
        · subst h₂
          by_cases h₁ : c₁ = 0
          · subst h₁
            rcases eq_or_ne β 0 with rfl | hβ
            · exact absurd (by ext i; rw [hc]; simp) hf0
            left
            refine nd_eq ?_ fun i hi => ?_
            · rw [hc]; simp [hβ, d₂]
            · rw [hc, hi₂ i hi]; simp
          · right; left
            refine nd_eq ?_ fun i hi => ?_
            · rw [hhigh _ le_rfl]; simp [h₁]
            · rw [hhigh i (by omega)]; simp [hi.ne']
        · right; right; left
          refine nd_eq ?_ fun i hi => ?_
          · rw [hhigh _ (by omega)]; simp [h₂, a₈]
          · have b₁ : i ≠ k - 1 := by omega
            rw [hhigh i (by omega)]; simp [hi.ne', b₁]
      · right; right; right; left
        refine nd_eq ?_ fun i hi => ?_
        · rw [hhigh _ (by omega)]; simp [h₃, a₄]
        · have b₁ : i ≠ k - 1 := by omega
          have b₂ : i ≠ k := by omega
          rw [hhigh i (by omega)]; simp [hi.ne', b₁, b₂]
    · right; right; right; right
      refine nd_eq ?_ fun i hi => ?_
      · rw [hhigh _ (by omega)]; simp [a₅, a₆, a₇, hα, d₁]
      · have b₁ : i ≠ k - 1 := by omega
        have b₂ : i ≠ k := by omega
        have b₃ : i ≠ k + 1 := by omega
        rw [hhigh i (by omega), hi₁ i hi]; simp [b₁, b₂, b₃]
