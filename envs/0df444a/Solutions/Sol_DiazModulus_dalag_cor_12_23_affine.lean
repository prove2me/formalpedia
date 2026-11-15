-- Prove2me | solution 1 for DiazModulus.dalag_cor_12_23_affine
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:31:26.453208+00:00
-- url     : https://prove2.me/submissions/484dcb30-8989-4671-8208-bc8ffb8c8e24

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_cor_12_23
import Theorems.Thm_DiazModulus_dalag_lemma_12_9_dehomog

open Complex ComplexConjugate

/-! # DALAG Cor. 12.23 in affine form

Let `M = M₀ + Σᵢ λᵢMᵢ` with rational matrices `M₀, …, M_m`, `λᵢ ∈ ℚ + ℒ`, and `1, λ₁, …, λ_m` free over `ℚ`.
Then `M = Σ_{j=0}^{m} eⱼNⱼ` with `e = (1, λ₁, …, λ_m)` and `N = (M₀, M₁, …, M_m)`; every `eⱼ` lies in `ℚ + ℒ`
(`1 − 1 = 0 = log 1`). The corollary in homogeneous form bounds the rank of `Σⱼ YⱼNⱼ` over `ℚ(Y₀, …, Y_m)` by
`2 · rank M`. Dehomogenisation gives the same rank for `M₀ + Σᵢ XᵢMᵢ` over `ℚ(X₁, …, X_m)`, which proves the
bound. The two rational structures on the fraction fields agree, as any two ring maps out of `ℚ` do. -/

open DiazModulus in
theorem solution {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (lam : Fin m → ℂ) (hlam : ∀ k, ∃ q : ℚ, lam k - q ∈ LogAlg)
    (hfree : LinearIndependent ℚ (Fin.cons 1 lam : Fin (m + 1) → ℂ))
    (M₀ : Matrix (Fin d) (Fin l) ℚ) (N : Fin m → Matrix (Fin d) (Fin l) ℚ)
    (hMN : M = M₀.map ((↑) : ℚ → ℂ) + ∑ k, lam k • (N k).map ((↑) : ℚ → ℂ)) :
    (M₀.map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ))) +
      ∑ k, (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)))).rank ≤ 2 * M.rank := by
  -- heL for e = Fin.cons 1 lam
  have heL : ∀ j, ∃ q : ℚ, (Fin.cons 1 lam : Fin (m + 1) → ℂ) j - q ∈ LogAlg := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · refine ⟨1, ?_⟩
      simp only [Fin.cons_zero, Rat.cast_one, sub_self]
      show IsAlgebraic ℚ (Complex.exp 0)
      rw [Complex.exp_zero]
      exact isAlgebraic_one
    · simpa only [Fin.cons_succ] using hlam i
  have hMN' : M = ∑ j, (Fin.cons 1 lam : Fin (m + 1) → ℂ) j •
      ((Fin.cons M₀ N : Fin (m + 1) → Matrix (Fin d) (Fin l) ℚ) j).map ((↑) : ℚ → ℂ) := by
    rw [Fin.sum_univ_succ, hMN]
    simp only [Fin.cons_zero, Fin.cons_succ, one_smul]
  have h6 := DiazModulus.dalag_cor_12_23 M _ hfree heL _ hMN'
  have h1 := DiazModulus.dalag_lemma_12_9_dehomog (k := ℚ) M₀ N
  -- bridge the two ℚ-algebra structures (`Subsingleton (Algebra ℚ _)` closes the instance goals)
  have h1' : (M₀.map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ))) +
      ∑ k, (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)))).rank =
      (∑ j : Fin (m + 1),
      (algebraMap (MvPolynomial (Fin (m + 1)) ℚ) (FractionRing (MvPolynomial (Fin (m + 1)) ℚ))
        (MvPolynomial.X j)) •
      ((Fin.cons M₀ N : Fin (m + 1) → Matrix (Fin d) (Fin l) ℚ) j).map
        (algebraMap ℚ (FractionRing (MvPolynomial (Fin (m + 1)) ℚ)))).rank := by
    convert h1 using 6
    all_goals first
      | exact RingHom.ext_rat _ _
      | exact congrArg DFunLike.coe (RingHom.ext_rat _ _)
      | exact Subsingleton.elim _ _
      | rfl
  rw [h1']
  exact h6
