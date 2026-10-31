-- Prove2me | solution 1 for DiazModulus.torusDeriv_mem_torusBox
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:06:28.209833+00:00
-- url     : https://prove2.me/submissions/efa081af-94be-4098-b6ce-414d21d61846

import Mathlib
import Definitions.Def_DiazMultiplicity

open Complex ComplexConjugate

/-! # The invariant derivations preserve the boxes and the torus ideal

Box: `torusBox T` is spanned by the monomials `m` whose block degrees `m.mapDomain β` (with `β = Sum.map id Prod.fst`)
are bounded by `T`, a condition stable under `m' ≤ m` (`Finsupp.mapDomain_add`). By `MvPolynomial.mkDerivation_monomial`,
`D_w (c X^m)` is a sum over the variables `v` in the support of `m` of `X^{m - e_v}` times `D_w X_v`. For `v = X_h` this
factor is the constant `ξ_h`, giving the monomial `m - e_v ≤ m`; for `v = Y_i, Z_i` it is `±η_i X_v`, giving back the
monomial `m` itself. So every term stays in the box, and so does `D_w f` for `f` in the box (`f = Σ c_m X^m`).
Torus ideal: `D_w (Y_i Z_i − 1) = Y_i (−η_i Z_i) + Z_i (η_i Y_i) = 0`, and the Leibniz rule
`D_w (r g) = r D_w g + g D_w r` keeps the span `(Y_i Z_i − 1)_i` stable (`Submodule.span_induction`). -/

namespace C13_O1
open DiazModulus MvPolynomial

theorem mapDomain_le_of_le {σ ι : Type*} (β : σ → ι) {m m' : σ →₀ ℕ} (h : m' ≤ m) (b : ι) :
    m'.mapDomain β b ≤ m.mapDomain β b := by
  have hm : m = m' + (m - m') := (add_tsub_cancel_of_le h).symm
  rw [hm, Finsupp.mapDomain_add, Finsupp.add_apply]
  exact Nat.le_add_right _ _

theorem torusDeriv_monomial_mem {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K))
    (S : Set (A₀ ⊕ (A₁ × Bool) →₀ ℕ)) (hS : ∀ m ∈ S, ∀ m', m' ≤ m → m' ∈ S)
    (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (hm : m ∈ S) (c : K) :
    torusDeriv w (monomial m c) ∈ restrictSupport K S := by
  rw [torusDeriv, mkDerivation_monomial]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun v hv => ?_)
  have hv1 : Finsupp.single v 1 ≤ m := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  rcases v with h | ⟨i, b⟩
  · simp only [Sum.elim_inl, smul_eq_mul, C_mul_monomial, mul_comm (monomial _ _) (C _), monomial_mem_restrictSupport]
    exact Or.inl (hS m hm _ tsub_le_self)
  · have hX : (X (Sum.inr (i, b)) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) = monomial (Finsupp.single _ 1) 1 := rfl
    have key : ∀ e : K, monomial (m - Finsupp.single (Sum.inr (i, b)) 1) (((m (Sum.inr (i, b))) : ℕ) : K) *
        (C e * X (Sum.inr (i, b))) ∈ restrictSupport K S := by
      intro e
      rw [hX, C_mul_monomial, monomial_mul, tsub_add_cancel_of_le hv1, monomial_mem_restrictSupport]
      exact Or.inl hm
    cases b
    · simpa only [Sum.elim_inr, Bool.false_eq_true, if_false, smul_eq_mul, mul_neg] using
        Submodule.neg_mem _ (key (w.2 i))
    · simpa only [Sum.elim_inr, if_true, smul_eq_mul] using key (w.2 i)

theorem torusDeriv_gen {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) (i : A₁) :
    torusDeriv w (X (Sum.inr (i, true)) * X (Sum.inr (i, false)) - 1 :
      MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) = 0 := by
  simp only [map_sub, Derivation.leibniz, Derivation.map_one_eq_zero, torusDeriv_X_inr, if_true,
    Bool.false_eq_true, if_false, smul_eq_mul, sub_zero]
  ring

end C13_O1

open DiazModulus C13_O1 in
theorem solution {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) :
    (∀ (T : A₀ ⊕ A₁ → ℕ) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), f ∈ torusBox K A₀ A₁ T → torusDeriv w f ∈ torusBox K A₀ A₁ T) ∧
      ∀ f ∈ torusIdeal K A₀ A₁, torusDeriv w f ∈ torusIdeal K A₀ A₁ := by
  constructor
  · intro T f hf
    have hS : ∀ m ∈ {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ | ∀ b, m.mapDomain (Sum.map id Prod.fst) b ≤ T b},
        ∀ m', m' ≤ m → m' ∈ {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ | ∀ b, m.mapDomain (Sum.map id Prod.fst) b ≤ T b} :=
      fun m hm m' h b => (mapDomain_le_of_le _ h b).trans (hm b)
    rw [torusBox, blockBox] at hf ⊢
    rw [f.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => torusDeriv_monomial_mem w _ hS m ?_ _
    exact ((MvPolynomial.mem_restrictSupport_iff K).mp hf) hm
  · intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [torusDeriv_gen]; exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x hx ih =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ (torusIdeal K A₀ A₁) hx)
