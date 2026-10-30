-- Prove2me | solution 1 for DiazModulus.torus_reduce_mem_restrictSupport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:12:27.099519+00:00
-- url     : https://prove2.me/submissions/e505fa74-6309-4faa-aca5-04250f839f27

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Reduction modulo the torus ideal inside the box

Write a monomial of `K[X, Y, Z]` as `X^a Y^b Z^c`. Its reduced form `red m` replaces, for every
`i`, the pair `(b_i, c_i)` by `(b_i − c_i, c_i − b_i)` (truncated subtraction) and keeps the
`X`-exponents. It is reduced (`min = 0`), it is `≤ m` coordinatewise, so it stays in the box
(the box condition is downward closed, `mapDomain` being additive), and it is unchanged when
`b_i` and `c_i` both go up by one.

Every monomial is congruent to its reduced form modulo `J₀ = (Y_i Z_i − 1)_i`: by strong
induction on the degree, if some `b_i, c_i` are both positive, `m = m' + e_{Y_i} + e_{Z_i}`,
`X^m − X^{m'} = X^{m'} (Y_i Z_i − 1) ∈ J₀`, `red m = red m'`, and `m'` has smaller degree.
Take `g = Σ_m f_m X^{red m}` (the image of `f` under `monomial m c ↦ monomial (red m) c`): it lies
in the box and is reduced, and `f − g = Σ_m f_m (X^m − X^{red m}) ∈ J₀`. -/

namespace C11_T2
open DiazModulus MvPolynomial

variable {A₀ A₁ : Type*}

/-- The `Y`/`Z` partner exponent that `red` subtracts (none for the `X` variables). -/
def partner (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (v : A₀ ⊕ (A₁ × Bool)) : ℕ :=
  Sum.elim (fun _ => 0) (fun q : A₁ × Bool => m (Sum.inr (q.1, !q.2))) v

/-- The reduced form of an exponent: `(a, b, c) ↦ (a, b − c, c − b)`. -/
noncomputable def red (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : A₀ ⊕ (A₁ × Bool) →₀ ℕ :=
  Finsupp.ofSupportFinite (fun v => m v - partner m v)
    (m.support.finite_toSet.subset fun v hv => by
      simp only [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff] at hv ⊢
      intro h0
      exact hv (by rw [h0, Nat.zero_sub]))

theorem red_apply (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (v : A₀ ⊕ (A₁ × Bool)) :
    red m v = m v - partner m v := rfl

theorem red_add_pair (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (i : A₁) :
    red (m + Finsupp.single (Sum.inr (i, true)) 1 + Finsupp.single (Sum.inr (i, false)) 1)
      = red m := by
  classical
  ext v
  rcases v with h | ⟨j, b⟩
  · simp [red_apply, partner]
  · by_cases hj : j = i
    · subst hj
      cases b <;> simp [red_apply, partner, Finsupp.single_apply]
    · simp [red_apply, partner, Finsupp.single_apply, Ne.symm hj]

theorem red_mem (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : red m ∈ torusReduced A₀ A₁ := by
  intro i
  simp only [red_apply, partner, Sum.elim_inr, Bool.not_true, Bool.not_false]
  omega

theorem red_mem_box (T : A₀ ⊕ A₁ → ℕ) {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ}
    (hm : ∀ b, m.mapDomain (Sum.map id Prod.fst) b ≤ T b) (b : A₀ ⊕ A₁) :
    (red m).mapDomain (Sum.map id Prod.fst) b ≤ T b := by
  have hle : red m ≤ m := fun v => Nat.sub_le _ _
  refine le_trans ?_ (hm b)
  conv_rhs => rw [← add_tsub_cancel_of_le hle]
  rw [Finsupp.mapDomain_add, Finsupp.add_apply]
  exact Nat.le_add_right _ _

theorem monomial_sub_red_mem (K : Type*) [Field K] (c : K) :
    ∀ (n : ℕ) (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ), m.degree = n →
      monomial m c - monomial (red m) c ∈ torusIdeal K A₀ A₁ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro m hn
  by_cases hm : m ∈ torusReduced A₀ A₁
  · have : red m = m := by
      ext v
      rcases v with h | ⟨i, b⟩
      · simp [red_apply, partner]
      · have := hm i
        cases b <;> simp only [red_apply, partner, Sum.elim_inr, Bool.not_true,
          Bool.not_false] <;> omega
    rw [this, sub_self]
    exact Ideal.zero_mem _
  · simp only [torusReduced, Set.mem_ofPred_eq, not_forall, not_or] at hm
    obtain ⟨i, hit, hif⟩ := hm
    set m' := m - Finsupp.single (Sum.inr (i, true)) 1 - Finsupp.single (Sum.inr (i, false)) 1
    have hm' : m' + Finsupp.single (Sum.inr (i, true)) 1 + Finsupp.single (Sum.inr (i, false)) 1
        = m := by
      ext v
      simp only [m', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h1 h2 h2 <;> subst_vars <;> simp_all <;> omega
    have hdeg : m'.degree < n := by
      rw [← hn, ← hm', map_add, map_add, Finsupp.degree_single, Finsupp.degree_single]
      omega
    have h1 := ih _ hdeg m' rfl
    have h2 : monomial m c - monomial m' c ∈ torusIdeal K A₀ A₁ := by
      have : monomial m c - monomial m' c = monomial m' c *
          (X (Sum.inr (i, true)) * X (Sum.inr (i, false)) - 1) := by
        rw [← hm', mul_sub, mul_one, X, X, ← mul_assoc, monomial_mul, monomial_mul, mul_one,
          mul_one]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hred : red m = red m' := by rw [← hm', red_add_pair]
    rw [hred]
    simpa using Ideal.add_mem _ h2 h1

end C11_T2

open DiazModulus C11_T2 in
theorem solution {K A₀ A₁ : Type*} [Field K] (T : A₀ ⊕ A₁ → ℕ) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
    (hf : f ∈ torusBox K A₀ A₁ T) :
    ∃ g ∈ torusBox K A₀ A₁ T ⊓ MvPolynomial.restrictSupport K (torusReduced A₀ A₁),
      f - g ∈ torusIdeal K A₀ A₁ := by
  classical
  refine ⟨∑ m ∈ f.support, MvPolynomial.monomial (red m) (MvPolynomial.coeff m f), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun m hm => Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [torusBox, blockBox, MvPolynomial.monomial_mem_restrictSupport]
      exact Or.inl (red_mem_box T (hf hm))
    · rw [MvPolynomial.monomial_mem_restrictSupport]
      exact Or.inl (red_mem m)
  · nth_rewrite 1 [f.as_sum]
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun m _ => monomial_sub_red_mem K _ _ m rfl
