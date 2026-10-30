-- Prove2me | solution 1 for DiazModulus.torus_coeff_poly
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:06:59.956983+00:00
-- url     : https://prove2.me/submissions/ec518771-2056-4780-b1c4-5dff04532102

import Mathlib
import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_torus_reduced_inf_eq_bot

open Complex ComplexConjugate

/-! # hME's coefficient polynomial in the torus model

Write `P_c = Σ_l c_l M_l` with `M_l = X^τ Π_i Y_i^{(s_i − D₁)₊} Z_i^{(D₁ − s_i)₊}`.
(1) Block boxes are multiplicative (`restrictSupport_add`, `Finsupp.mapDomain_add`), and
`W_v^k` lies in the box `Pi.single (β v) k`, so `M_l` lies in the box with `X_h`-degree `τ_h ≤ D₀`
and `(Y_i, Z_i)`-degree `(s_i − D₁)₊ + (D₁ − s_i)₊ ≤ D₁` (as `s_i ≤ 2D₁`); `blockBox_mono` and
`sum_mem` finish. (2) `M_l` is the monomial `X^{e(l)}` (`MvPolynomial.monomial_eq`,
`Finsupp.prod_fintype`, `Fintype.prod_sum_type`), with `e(l)` reduced (one of the two
truncated differences vanishes), so `P_c` lies in the reduced span; if `P_c ∈ J₀`,
`torus_reduced_inf_eq_bot` (T3) gives `P_c = 0`, and since `l ↦ e(l)` is injective
(`s = D₁ + (s − D₁)₊ − (D₁ − s)₊`) the coefficient of `X^{e(l)}` in `P_c` is `c_l`, so `c = 0`.
(3) `eval` is a ring map: `M_l ↦ x^τ Π_i y_i^{(s_i−D₁)₊}(y_i⁻¹)^{(D₁−s_i)₊} = x^τ Π_i y_i^{s_i − D₁}`
by `zpow_add₀` and `zpow_neg`. -/

namespace C11_T7
open DiazModulus MvPolynomial

variable {K : Type*} [Field K]

theorem box_mul {σ ι : Type*} (β : σ → ι) {f g : MvPolynomial σ K} {T T' : ι → ℕ}
    (hf : f ∈ blockBox K β T) (hg : g ∈ blockBox K β T') : f * g ∈ blockBox K β (T + T') := by
  have := Submodule.mul_mem_mul hf hg
  unfold blockBox at this ⊢
  rw [← restrictSupport_add] at this
  refine restrictSupport_mono K ?_ this
  rintro _ ⟨u, hu, w, hw, rfl⟩ b
  rw [Finsupp.mapDomain_add, Finsupp.add_apply, Pi.add_apply]
  exact add_le_add (hu b) (hw b)

theorem box_prod {σ ι ι' : Type*} (β : σ → ι) (s : Finset ι') (f : ι' → MvPolynomial σ K)
    (T : ι' → ι → ℕ) (h : ∀ j ∈ s, f j ∈ blockBox K β (T j)) :
    ∏ j ∈ s, f j ∈ blockBox K β (∑ j ∈ s, T j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_blockBox_zero K β
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact box_mul β (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem X_pow_mem {σ ι : Type*} [DecidableEq ι] (β : σ → ι) (v : σ) (k : ℕ) :
    (X v : MvPolynomial σ K) ^ k ∈ blockBox K β (Pi.single (β v) k) := by
  rw [X_pow_eq_monomial, blockBox, monomial_mem_restrictSupport]
  left
  intro b
  rw [Finsupp.mapDomain_single, Finsupp.single_eq_pi_single]

theorem unit_pow (y : Kˣ) (s D : ℕ) :
    (y : K) ^ (s - D) * ((y⁻¹ : Kˣ) : K) ^ (D - s) = (y : K) ^ ((s : ℤ) - D) := by
  have : ((s : ℤ) - D) = ((s - D : ℕ) : ℤ) + (-((D - s : ℕ) : ℤ)) := by omega
  rw [this, zpow_add₀ (Units.ne_zero y), zpow_neg, zpow_natCast, zpow_natCast,
    Units.val_inv_eq_inv_val, inv_pow]

variable {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁]

/-- The exponent of the monomial `M_l`. -/
noncomputable def expo (D₀ D₁ : ℕ) (l : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1))) :
    A₀ ⊕ (A₁ × Bool) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun h => (l.1 h : ℕ))
    fun p => if p.2 then (l.2 p.1 : ℕ) - D₁ else D₁ - (l.2 p.1 : ℕ))

theorem monomial_expo (D₀ D₁ : ℕ) (l : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1))) :
    monomial (expo D₀ D₁ l) (1 : K) = (∏ h, X (Sum.inl h) ^ (l.1 h : ℕ)) *
      ∏ i, (X (Sum.inr (i, true)) ^ ((l.2 i : ℕ) - D₁) * X (Sum.inr (i, false)) ^ (D₁ - (l.2 i : ℕ))) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp [expo]

theorem expo_injective (D₀ D₁ : ℕ) : Function.Injective (expo (A₀ := A₀) (A₁ := A₁) D₀ D₁) := by
  intro l l' h
  have hv : ∀ v, expo D₀ D₁ l v = expo D₀ D₁ l' v := fun v => by rw [h]
  ext1
  · funext a
    exact Fin.ext (by simpa [expo] using hv (Sum.inl a))
  · funext i
    have h1 := hv (Sum.inr (i, true))
    have h2 := hv (Sum.inr (i, false))
    simp only [expo, Finsupp.coe_equivFunOnFinite_symm, Sum.elim_inr, if_true] at h1 h2
    simp only [Bool.false_eq_true, if_false] at h2
    exact Fin.ext (by omega)

end C11_T7

open DiazModulus C11_T7 in
theorem solution {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁]
    [DecidableEq A₀] [DecidableEq A₁] (D₀ D₁ : ℕ) (c : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → K) :
    torusCoeffPoly D₀ D₁ c ∈ torusBox K A₀ A₁ (boxD A₀ A₁ D₀ D₁) ∧
    (c ≠ 0 → torusCoeffPoly D₀ D₁ c ∉ torusIdeal K A₀ A₁) ∧
    ∀ (x : A₀ → K) (y : A₁ → Kˣ), MvPolynomial.eval (torusPoint x y) (torusCoeffPoly D₀ D₁ c)
      = ∑ l, c l * ((∏ h, x h ^ (l.1 h : ℕ)) * ∏ i, (y i : K) ^ (((l.2 i : ℕ) : ℤ) - D₁)) := by
  have hP : torusCoeffPoly (K := K) D₀ D₁ c = ∑ l, c l • MvPolynomial.monomial (expo D₀ D₁ l) 1 := by
    simp only [monomial_expo]; rfl
  refine ⟨?_, ?_, ?_⟩
  · -- the box
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    set β : A₀ ⊕ (A₁ × Bool) → A₀ ⊕ A₁ := Sum.map id Prod.fst
    have hm := box_mul (K := K) β
      (box_prod β Finset.univ _ _ fun h _ => X_pow_mem β (Sum.inl h) (l.1 h : ℕ))
      (box_prod β Finset.univ _ _ fun i _ =>
        box_mul β (X_pow_mem β (Sum.inr (i, true)) ((l.2 i : ℕ) - D₁))
          (X_pow_mem β (Sum.inr (i, false)) (D₁ - (l.2 i : ℕ))))
    refine blockBox_mono K β ?_ hm
    intro b
    cases b with
    | inl a =>
      simp [β, Finset.sum_apply, Pi.single_apply]
      exact Nat.lt_succ_iff.mp (l.1 a).isLt
    | inr j =>
      simp [β, Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
      have := (l.2 j).isLt
      omega
  · -- not in J₀
    intro hc hJ
    have hR : torusCoeffPoly (K := K) D₀ D₁ c ∈ MvPolynomial.restrictSupport K (torusReduced A₀ A₁) := by
      rw [hP]
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
      rw [MvPolynomial.monomial_mem_restrictSupport]
      left
      intro i
      simp only [expo, Finsupp.coe_equivFunOnFinite_symm, Sum.elim_inr, if_true,
        Bool.false_eq_true, if_false]
      omega
    have h0 : torusCoeffPoly (K := K) D₀ D₁ c = 0 := by
      have := DiazModulus.torus_reduced_inf_eq_bot (K := K) (A₀ := A₀) (A₁ := A₁)
      rw [← Submodule.mem_bot K, ← this]
      exact ⟨hR, hJ⟩
    apply hc
    funext l₀
    have := congrArg (MvPolynomial.coeff (expo D₀ D₁ l₀)) (hP.symm.trans h0)
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single l₀] at this
    · simpa using this
    · intro l _ hl
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
        if_neg fun h => hl (expo_injective D₀ D₁ h), smul_zero]
    · intro h; exact absurd (Finset.mem_univ l₀) h
  · -- evaluation
    intro x y
    simp only [torusCoeffPoly, map_sum, MvPolynomial.smul_eval, map_mul, map_prod, map_pow,
      MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [torusPoint, Sum.elim_inr, if_true, Bool.false_eq_true, if_false]
    exact unit_pow (y i) _ _
