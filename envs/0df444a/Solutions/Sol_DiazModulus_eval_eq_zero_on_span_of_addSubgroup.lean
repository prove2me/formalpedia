-- Prove2me | solution 1 for DiazModulus.eval_eq_zero_on_span_of_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:06:22.842623+00:00
-- url     : https://prove2.me/submissions/8709e61b-35dd-4605-b0ba-2cee9866bf13

import Mathlib

open Complex ComplexConjugate

/-! # A polynomial vanishing on an additive subgroup vanishes on its complex span

Write `z ∈ span_ℂ Λ` as `Σ_{i < n} c_i x_i` with `x_i ∈ Λ` (`Submodule.mem_span_set'`) and prove, by induction on
`n` and for every base point `y ∈ Λ`, that `F(y + Σ c_i x_i) = 0`. For `n = 0` this is the hypothesis. In the step,
peel off `c_0 x_0` and put `r = Σ_{i ≥ 1} c_i x_i`: the one-variable polynomial `q(t) = F(y + r + t x_0)` (the
evaluation of `F` at the polynomial point `y + r + t·x_0`) vanishes at every integer `t = k`, by the induction
hypothesis at the base point `y + k x_0 ∈ Λ`. A complex polynomial with infinitely many roots is zero
(`Polynomial.eq_zero_of_infinite_isRoot`), so `q(c_0) = 0`; the case `y = 0` is the claim. -/

namespace C13_G2

/-- Evaluating `F` at a point of `(ℂ[t])^{A₀}` and then at `t` is evaluating `F` at the values. -/
theorem eval_eval₂_C {A₀ : Type*} (g : A₀ → Polynomial ℂ) (F : MvPolynomial A₀ ℂ) (t : ℂ) :
    (MvPolynomial.eval₂ Polynomial.C g F).eval t = MvPolynomial.eval (fun a => (g a).eval t) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [MvPolynomial.eval₂_add, hp, hq]
  | mul_X p a hp => simp [MvPolynomial.eval₂_mul, hp]

/-- The induction on the length of a linear combination, with a moving base point in `Λ`. -/
theorem eval_add_sum_eq_zero {A₀ : Type*} (Λ : AddSubgroup (A₀ → ℂ)) (F : MvPolynomial A₀ ℂ)
    (hF : ∀ x ∈ Λ, MvPolynomial.eval x F = 0) (n : ℕ) :
    ∀ (c : Fin n → ℂ) (x : Fin n → (Λ : Set (A₀ → ℂ))) (y : A₀ → ℂ), y ∈ Λ →
      MvPolynomial.eval (y + ∑ i, c i • (x i : A₀ → ℂ)) F = 0 := by
  induction n with
  | zero => intro c x y hy; simpa using hF y hy
  | succ n ih =>
    intro c x y hy
    rw [Fin.sum_univ_succ]
    set r : A₀ → ℂ := ∑ i : Fin n, c i.succ • (x i.succ : A₀ → ℂ)
    set x₀ : A₀ → ℂ := (x 0 : A₀ → ℂ)
    have hx₀ : x₀ ∈ Λ := (x 0).2
    let q : Polynomial ℂ := MvPolynomial.eval₂ Polynomial.C
      (fun a => Polynomial.C (y a + r a) + Polynomial.C (x₀ a) * Polynomial.X) F
    have hq : ∀ t : ℂ, q.eval t = MvPolynomial.eval (y + t • x₀ + r) F := by
      intro t
      rw [eval_eval₂_C]
      congr 2
      funext a
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hroot : ∀ k : ℤ, q.IsRoot (k : ℂ) := by
      intro k
      have hmem : y + (k : ℂ) • x₀ ∈ Λ := by
        have : (k : ℂ) • x₀ = k • x₀ := by
          funext a; simp [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
        rw [this]
        exact Λ.add_mem hy (Λ.zsmul_mem hx₀ k)
      rw [Polynomial.IsRoot, hq]
      exact ih (fun i => c i.succ) (fun i => x i.succ) _ hmem
    have hq0 : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : ℂ))
      · intro a b hab; simpa using hab
      · intro k; exact hroot k
    have := hq (c 0)
    rw [hq0, Polynomial.eval_zero] at this
    rw [← add_assoc]
    exact this.symm

end C13_G2

open C13_G2 in
theorem solution {A₀ : Type*} (Λ : AddSubgroup (A₀ → ℂ)) (F : MvPolynomial A₀ ℂ)
    (hF : ∀ x ∈ Λ, MvPolynomial.eval x F = 0) :
    ∀ x ∈ Submodule.span ℂ (Λ : Set (A₀ → ℂ)), MvPolynomial.eval x F = 0 := by
  intro z hz
  obtain ⟨n, c, x, rfl⟩ := Submodule.mem_span_set'.mp hz
  simpa using eval_add_sum_eq_zero Λ F hF n c x 0 Λ.zero_mem
