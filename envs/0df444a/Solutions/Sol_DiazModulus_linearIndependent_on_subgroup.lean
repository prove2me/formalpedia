-- Prove2me | solution 1 for DiazModulus.linearIndependent_on_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:50.414529+00:00
-- url     : https://prove2.me/submissions/113906cc-fcb5-448c-847e-81dd5f646f04

import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_eval_eq_zero_of_sum_mul_char
import Theorems.Thm_DiazModulus_eval_eq_zero_on_span_of_addSubgroup

open Complex ComplexConjugate

/-! # Reduced polynomials in `X_H, Y_J, Z_J` vanishing on a subgroup are zero

A reduced monomial `X^a Y^b Z^c` takes the value `x_g^a · y_g^λ` at `torusPt g`, with `λ = b − c ∈ ℤ^{A₁}`, and
`(a, λ)` determines the monomial (reducedness: `min(b_i, c_i) = 0`). Group the monomials of `f` by `λ`: on `Γ`,
`f(torusPt g) = Σ_λ F_λ(x_g) χ_λ(g)` with `F_λ ∈ ℂ[X_{A₀}]` and the characters `χ_λ(g) = Π_i y_{g,i}^{λ_i}` of `Γ`.
The `λ` that occur vanish off `J`, so `χ_λ = χ_λ′` forces `λ − λ′ ∈ ℤ^J` to kill `Γ`, hence `λ = λ′` by `hJ`: the
characters are distinct. The imported node `eval_eq_zero_of_sum_mul_char` (G1, with `ρ(g) = x_g`) gives
`F_λ(x_g) = 0` on `Γ`, and `eval_eq_zero_on_span_of_addSubgroup` (G2, for the additive subgroup `{x_g : g ∈ Γ}`)
extends this to its complex span. `F_λ` involves only the variables `X_h`, `h ∈ H`, and by `hH` every point agrees on
`H` with a point of the span, so `F_λ` vanishes everywhere and is `0` (`MvPolynomial.funext`). The coefficient of
`X^a` in `F_λ` is the coefficient of the unique monomial of `f` with data `(a, λ)`, so all coefficients of `f` vanish. -/

namespace C13_G6
open DiazModulus

/-- The exponent `λ = b − c` of a monomial `X^a Y^b Z^c`. -/
def lam {A₀ A₁ : Type*} (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : A₁ → ℤ :=
  fun i => (m (Sum.inr (i, true)) : ℤ) - m (Sum.inr (i, false))

/-- The exponent `a` of a monomial `X^a Y^b Z^c`. -/
noncomputable def xpart {A₀ A₁ : Type*} (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : A₀ →₀ ℕ :=
  Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn

/-- The character `g ↦ y_g^λ` of a subgroup. -/
noncomputable def chi {A₀ A₁ : Type*} [Fintype A₁] (l : A₁ → ℤ) (Γ : Subgroup (TorusGroup ℂ A₀ A₁)) : ↥Γ →* ℂˣ where
  toFun g := ∏ i, (g : TorusGroup ℂ A₀ A₁).2 i ^ l i
  map_one' := by simp
  map_mul' g g' := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem eval_xpart {A₀ A₁ : Type*} [Fintype A₀] (x : A₀ → ℂ) (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (c : ℂ) :
    MvPolynomial.eval x (MvPolynomial.monomial (xpart m) c) = c * ∏ h, x h ^ m (Sum.inl h) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp [xpart, Finsupp.comapDomain_apply]

/-- The value of a monomial at a torus point. -/
theorem eval_torusPt_monomial {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (g : TorusGroup ℂ A₀ A₁)
    (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (c : ℂ) :
    MvPolynomial.eval (torusPt g) (MvPolynomial.monomial m c) =
      MvPolynomial.eval (Multiplicative.toAdd g.1) (MvPolynomial.monomial (xpart m) c) *
        ((∏ i, g.2 i ^ lam m i : ℂˣ) : ℂ) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, eval_xpart,
    Fintype.prod_prod_type, mul_assoc]
  congr 2
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hu : g.2 i ^ lam m i = g.2 i ^ m (Sum.inr (i, true)) * (g.2 i)⁻¹ ^ m (Sum.inr (i, false)) := by
    rw [lam, zpow_sub, zpow_natCast, zpow_natCast, inv_pow]
  rw [hu, Fintype.prod_bool]
  simp [torusPt, torusPoint]

/-- A reduced monomial is determined by `(a, λ)`. -/
theorem eq_of_reduced {A₀ A₁ : Type*} {m m' : A₀ ⊕ (A₁ × Bool) →₀ ℕ} (hm : m ∈ torusReduced A₀ A₁)
    (hm' : m' ∈ torusReduced A₀ A₁) (hx : xpart m = xpart m') (hl : lam m = lam m') : m = m' := by
  ext p
  rcases p with h | ⟨i, b⟩
  · have := DFunLike.congr_fun hx h
    simpa [xpart, Finsupp.comapDomain_apply] using this
  · have h1 := congrFun hl i
    simp only [lam] at h1
    rcases hm i with h2 | h2 <;> rcases hm' i with h3 | h3 <;> cases b <;> omega

end C13_G6

open DiazModulus C13_G6 in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁)) (H : Finset A₀)
    (J : Finset A₁) (hH : ∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h)
    (hJ : ∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0)
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (hf : f ∈ MvPolynomial.restrictSupport ℂ (torusReduced A₀ A₁))
    (hfH : ∀ m ∈ f.support, (∀ h ∉ H, m (Sum.inl h) = 0) ∧ ∀ i ∉ J, ∀ b, m (Sum.inr (i, b)) = 0)
    (hΓ : ∀ g ∈ Γ, MvPolynomial.eval (torusPt g) f = 0) :
    f = 0 := by
  classical
  have hred : ∀ m ∈ f.support, m ∈ torusReduced A₀ A₁ :=
    fun m hm => (show (↑f.support : Set _) ⊆ torusReduced A₀ A₁ from hf) (Finset.mem_coe.mpr hm)
  let S : Finset (A₁ → ℤ) := f.support.image lam
  let F : ↥S → MvPolynomial A₀ ℂ := fun l =>
    ∑ m ∈ f.support.filter (fun m => lam m = l), MvPolynomial.monomial (xpart m) (f.coeff m)
  let ρ : ↥Γ →* Multiplicative (A₀ → ℂ) := (MonoidHom.fst _ _).comp Γ.subtype
  let χ : ↥S → (↥Γ →* ℂˣ) := fun l => chi (l : A₁ → ℤ) Γ
  have hlamJ : ∀ l ∈ S, ∀ i ∉ J, l i = 0 := by
    intro l hl i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    simp [lam, (hfH m hm).2 i hi true, (hfH m hm).2 i hi false]
  have hχ : Function.Injective χ := by
    intro l l' hll
    apply Subtype.ext
    have h0 : (l : A₁ → ℤ) - l' = 0 := by
      refine hJ _ (fun i hi => by simp [hlamJ _ l.2 i hi, hlamJ _ l'.2 i hi]) fun g hg => ?_
      have := DFunLike.congr_fun hll ⟨g, hg⟩
      change ∏ i, g.2 i ^ (l : A₁ → ℤ) i = ∏ i, g.2 i ^ (l' : A₁ → ℤ) i at this
      simp only [Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib, this, mul_inv_cancel]
    exact sub_eq_zero.mp h0
  -- the grouped identity on `Γ`
  have hsum : ∀ g : ↥Γ, ∑ c, MvPolynomial.eval (Multiplicative.toAdd (ρ g)) (F c) * (χ c g : ℂ) = 0 := by
    intro g
    have e1 := hΓ g g.2
    conv_lhs at e1 => rw [f.as_sum, map_sum]
    refine Eq.trans ?_ e1
    refine (Finset.sum_coe_sort S (fun l => MvPolynomial.eval (Multiplicative.toAdd (g : TorusGroup ℂ A₀ A₁).1)
      (∑ m ∈ f.support.filter (fun m => lam m = l), MvPolynomial.monomial (xpart m) (f.coeff m)) *
        ((chi l Γ g : ℂˣ) : ℂ))).trans ?_
    rw [← Finset.sum_fiberwise_of_maps_to (s := f.support) (t := S) (g := lam)
      (fun m hm => Finset.mem_image_of_mem lam hm)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_torusPt_monomial, ← (Finset.mem_filter.mp hm).2]
    rfl
  have key := DiazModulus.eval_eq_zero_of_sum_mul_char ρ χ hχ F hsum
  -- the additive subgroup `{x_g : g ∈ Γ}`
  let Λ : AddSubgroup (A₀ → ℂ) :=
    { carrier := {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}
      zero_mem' := ⟨1, Γ.one_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
        exact ⟨g * g', Γ.mul_mem hg hg', rfl⟩
      neg_mem' := by
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨g⁻¹, Γ.inv_mem hg, rfl⟩ }
  have hF0 : ∀ c, F c = 0 := by
    intro c
    have hspan := DiazModulus.eval_eq_zero_on_span_of_addSubgroup Λ (F c)
      (by rintro _ ⟨g, hg, rfl⟩; exact key c ⟨g, hg⟩)
    apply MvPolynomial.funext
    intro x
    obtain ⟨v, hv, hvx⟩ := hH x
    rw [map_zero, ← hspan v hv]
    simp only [F, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmH := (hfH m (Finset.mem_filter.mp hm).1).1
    rw [eval_xpart, eval_xpart]
    congr 1
    refine Finset.prod_congr rfl fun h _ => ?_
    by_cases hh : h ∈ H
    · rw [hvx h hh]
    · rw [hmH h hh, pow_zero, pow_zero]
  -- read off the coefficients
  ext m
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  have hm : m ∈ f.support := MvPolynomial.mem_support_iff.mpr hne
  have hl : lam m ∈ S := Finset.mem_image_of_mem lam hm
  have hc := congrArg (MvPolynomial.coeff (xpart m)) (hF0 ⟨lam m, hl⟩)
  simp only [F, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single m] at hc
  · simp at hc; exact hne hc
  · intro m' hm' hne'
    rw [if_neg]
    intro hx
    exact hne' (eq_of_reduced (hred m' (Finset.mem_filter.mp hm').1) (hred m hm) hx
      (Finset.mem_filter.mp hm').2)
  · intro h; exact (h (Finset.mem_filter.mpr ⟨hm, rfl⟩)).elim
