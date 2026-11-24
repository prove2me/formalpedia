-- Prove2me | solution 1 for Formalism.L2.LamCM.subst_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:28.914863+00:00
-- url     : https://prove2.me/submissions/8e13319e-9b65-42be-9383-37199c26f92c

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
open scoped ComplexOrder
namespace Formalism.L2.LamCM
private theorem eval_bind₁' {σ τ : Type} (f : σ → MvPolynomial τ ℂ) (x : τ → ℂ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.bind₁ f P) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) P := by
  induction P using MvPolynomial.induction_on <;> simp_all
private theorem coeff_bind_scale {σ : Type} [Fintype σ] (c : ℂ) (P : MvPolynomial σ ℂ) (μ : σ →₀ ℕ) :
    MvPolynomial.coeff μ (MvPolynomial.bind₁ (fun v => MvPolynomial.C c * MvPolynomial.X v) P) =
      c ^ (∑ v, μ v) * MvPolynomial.coeff μ P := by
  classical
  refine MvPolynomial.induction_on' P (fun ν b => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.bind₁_monomial]
    have hprod : ∏ i ∈ ν.support, (MvPolynomial.C c * MvPolynomial.X i) ^ ν i =
        MvPolynomial.C (c ^ (∑ v, ν v)) * MvPolynomial.monomial ν (1 : ℂ) := by
      rw [← MvPolynomial.prod_X_pow_eq_monomial]
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum]
      congr 3
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
    rw [hprod, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  · simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]
private theorem degree_of_scale {σ : Type} [Fintype σ] (P Δ : MvPolynomial σ ℂ) (n : ℕ) (x0 : σ → ℂ)
    (hx0 : MvPolynomial.eval x0 Δ ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Δ ≠ 0 → MvPolynomial.eval (fun v => 2 * x v) P = 2 ^ n * MvPolynomial.eval x P) :
    ∀ μ : σ →₀ ℕ, MvPolynomial.coeff μ P ≠ 0 → ∑ v, μ v = n := by
  intro μ hμ
  set Q := MvPolynomial.bind₁ (fun v => MvPolynomial.C (2 : ℂ) * MvPolynomial.X v) P -
    MvPolynomial.C ((2 : ℂ) ^ n) * P with hQ
  have hevQ : ∀ x, MvPolynomial.eval x (Δ * Q) = 0 := by
    intro x
    rw [map_mul]
    by_cases hx : MvPolynomial.eval x Δ = 0
    · rw [hx, zero_mul]
    · rw [hQ, map_sub, eval_bind₁']
      simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [h x hx, sub_self, mul_zero]
  have hΔQ : Δ * Q = 0 := MvPolynomial.funext fun x => by rw [hevQ x, map_zero]
  have hΔ : Δ ≠ 0 := by
    intro h0
    apply hx0
    rw [h0, map_zero]
  have hQ0 : Q = 0 := (mul_eq_zero.mp hΔQ).resolve_left hΔ
  have hc := congrArg (MvPolynomial.coeff μ) hQ0
  rw [hQ, MvPolynomial.coeff_sub, coeff_bind_scale, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero,
    sub_eq_zero] at hc
  have h2 : (2 : ℂ) ^ (∑ v, μ v) = 2 ^ n := mul_right_cancel₀ hμ hc
  have h3 : ((2 ^ (∑ v, μ v) : ℕ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := by
    push_cast
    exact h2
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h3)
private theorem eval_scale_of_degree {σ : Type} [Fintype σ] (P : MvPolynomial σ ℂ) (n : ℕ)
    (h : ∀ μ : σ →₀ ℕ, MvPolynomial.coeff μ P ≠ 0 → ∑ v, μ v = n) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun v => c * x v) P = c ^ n * MvPolynomial.eval x P := by
  have hb : MvPolynomial.bind₁ (fun v => MvPolynomial.C c * MvPolynomial.X v) P = MvPolynomial.C (c ^ n) * P := by
    ext μ
    rw [coeff_bind_scale, MvPolynomial.coeff_C_mul]
    by_cases hμ : MvPolynomial.coeff μ P = 0
    · simp [hμ]
    · rw [h μ hμ]
  have h1 := eval_bind₁' (fun v => MvPolynomial.C c * MvPolynomial.X v) x P
  rw [hb] at h1
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
  exact h1.symm
private theorem evalFr_matOf {B : Type} {m : B → ℕ} (P : MvPolynomial (FrVar m) ℂ) (x : FrVar m → ℂ) :
    evalFr P (matOf x) = MvPolynomial.eval x P := rfl
private theorem smul_one_blockTriangular {n : ℕ} (c : ℂ) :
    (c • (1 : Matrix (Fin n) (Fin n) ℂ)).BlockTriangular id := by
  intro i j hij
  have h : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  simp [Matrix.one_apply_ne h]
private theorem evalFr_two_smul {B : Type} [Fintype B] [DecidableEq B] {m : B → ℕ} (a : ∀ b, Fin (m b) → ℕ)
    (P : MvPolynomial (FrVar m) ℂ) (heq : IsEquiv a P) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ)
    (hX : ∀ b, (X b).det ≠ 0) :
    evalFr P (fun b => (2 : ℂ) • X b) = 2 ^ (∑ b, ∑ i, a b i) * evalFr P X := by
  classical
  have key : ∀ s : Finset B, evalFr P (fun b => if b ∈ s then (2 : ℂ) • X b else X b) =
      2 ^ (∑ b ∈ s, ∑ i, a b i) * evalFr P X := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro b0 s hb0 ih
      have hupd : (fun b => if b ∈ insert b0 s then (2 : ℂ) • X b else X b) =
          Function.update (fun b => if b ∈ s then (2 : ℂ) • X b else X b) b0
            ((if b0 ∈ s then (2 : ℂ) • X b0 else X b0) * ((2 : ℂ) • (1 : Matrix (Fin (m b0)) (Fin (m b0)) ℂ))) := by
        funext b
        by_cases h : b = b0
        · subst h
          simp [hb0]
        · simp [h]
      have hdet : ∀ b', (if b' ∈ s then (2 : ℂ) • X b' else X b').det ≠ 0 := by
        intro b'
        by_cases h : b' ∈ s
        · simp only [h, if_true, Matrix.det_smul]
          exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (hX b')
        · simp only [h, if_false]
          exact hX b'
      have h2 : ((2 : ℂ) • (1 : Matrix (Fin (m b0)) (Fin (m b0)) ℂ)).det ≠ 0 := by
        rw [Matrix.det_smul, Matrix.det_one, mul_one]
        exact pow_ne_zero _ two_ne_zero
      have htri : ReciprocityTheory.MultiplicativeHeights.triChar (a b0) ((2 : ℂ) • (1 : Matrix (Fin (m b0)) (Fin (m b0)) ℂ)) =
          2 ^ (∑ i, a b0 i) := by
        unfold ReciprocityTheory.MultiplicativeHeights.triChar
        simp [Finset.prod_pow_eq_pow_sum]
      rw [hupd, heq _ b0 _ hdet h2 (smul_one_blockTriangular 2), ih, Finset.sum_insert hb0, pow_add, htri]
      ring
  simpa using key Finset.univ
end Formalism.L2.LamCM
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.LamCM
namespace Formalism.L2.LamCM
theorem _root_.solution : SubstHomog := by
  unfold SubstHomog
  intro B _ _ m a P U heq μ hμ
  classical
  set N := ∑ b, ∑ i, a b i with hN
  set Δ : MvPolynomial (FrVar m) ℂ :=
    ∏ b, (Matrix.of fun k i => (MvPolynomial.X (⟨b, (i, k)⟩ : FrVar m) : MvPolynomial (FrVar m) ℂ)).det with hΔ
  have hevΔ : ∀ x : FrVar m → ℂ, MvPolynomial.eval x Δ = ∏ b, (matOf x b).det := by
    intro x
    rw [hΔ, map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext k i
    simp [matOf]
  have hP : ∀ ν : FrVar m →₀ ℕ, MvPolynomial.coeff ν P ≠ 0 → ∑ v, ν v = N := by
    refine degree_of_scale P Δ N (fun v => if v.2.1 = v.2.2 then 1 else 0) ?_ ?_
    · rw [hevΔ]
      refine Finset.prod_ne_zero_iff.mpr fun b _ => ?_
      have h1 : matOf (fun v : FrVar m => if v.2.1 = v.2.2 then (1 : ℂ) else 0) b = 1 := by
        ext k i
        by_cases h : k = i
        · subst h
          simp [matOf]
        · simp [matOf, Matrix.one_apply_ne h, Ne.symm h]
      rw [h1, Matrix.det_one]
      exact one_ne_zero
    · intro x hx
      rw [hevΔ] at hx
      have hXd : ∀ b, (matOf x b).det ≠ 0 := fun b => Finset.prod_ne_zero_iff.mp hx b (Finset.mem_univ _)
      rw [← evalFr_matOf, ← evalFr_matOf]
      have h1 : matOf (fun v => 2 * x v) = fun b => (2 : ℂ) • matOf x b := by
        funext b
        ext k i
        simp [matOf]
      rw [h1]
      exact evalFr_two_smul a P heq (matOf x) hXd
  refine degree_of_scale (substFr U P) 1 N (fun _ => 0) (by simp) ?_ μ hμ
  intro x _
  unfold substFr
  rw [eval_bind₁', eval_bind₁']
  have hlin : ∀ v : FrVar m, MvPolynomial.eval (fun w => 2 * x w)
      (∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) =
      2 * MvPolynomial.eval x (∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) := by
    intro v
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hlin]
  exact eval_scale_of_degree P N hP 2 _
end Formalism.L2.LamCM
