-- Prove2me | solution 1 for DissipativePrep.Unique.dprime_eq_dark
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:03:08.888305+00:00
-- url     : https://prove2.me/submissions/31da64e9-f014-40b5-9736-66d1a56b3d5d

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16 DissipativePrep.Unique

theorem solution {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) :
    {ψ : EuclideanSpace ℂ (Fin d) | ∃ lam : ℝ, act (Qop H c g)ᴴ ψ = (Complex.I * lam) • ψ} =
      {ψ | (∀ l, act (c l) ψ = 0) ∧ ∃ E : ℝ, act H ψ = (E : ℂ) • ψ} := by
  have hQ : (Qop H c g)ᴴ = Pop c g + Complex.I • H := by
    unfold Qop Pop
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq, Matrix.conjTranspose_sum]
    have : star Complex.I = -Complex.I := by simp
    rw [this, neg_smul, sub_neg_eq_add]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp
  have hPv : ∀ v : Fin d → ℂ, Pop c g *ᵥ v = ∑ l, ((g l : ℝ) : ℂ) • ((c l)ᴴ *ᵥ (c l *ᵥ v)) := by
    intro v
    unfold Pop
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hdot : ∀ (C : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ),
      star v ⬝ᵥ (Cᴴ *ᵥ (C *ᵥ v)) = star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := by
    intro C v
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hBreal : ∀ v : Fin d → ℂ, (star v ⬝ᵥ (H *ᵥ v)).im = 0 := by
    intro v
    have e : star (star v ⬝ᵥ (H *ᵥ v)) = star v ⬝ᵥ (H *ᵥ v) := by
      rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
    have := congrArg Complex.im e
    simp at this
    linarith
  have hact : ∀ (M : Matrix (Fin d) (Fin d) ℂ) (r : ℂ) (ψ : EuclideanSpace ℂ (Fin d)),
      act M ψ = r • ψ ↔ M *ᵥ WithLp.ofLp ψ = r • WithLp.ofLp ψ := by
    intro M r ψ
    constructor
    · intro h; have := congrArg WithLp.ofLp h; simpa [act] using this
    · intro h; apply WithLp.ofLp_injective; simpa [act] using h
  have hact0 : ∀ (M : Matrix (Fin d) (Fin d) ℂ) (ψ : EuclideanSpace ℂ (Fin d)),
      act M ψ = 0 ↔ M *ᵥ WithLp.ofLp ψ = 0 := by
    intro M ψ
    constructor
    · intro h; have := congrArg WithLp.ofLp h; simpa [act] using this
    · intro h; apply WithLp.ofLp_injective; simpa [act] using h
  have hQv : ∀ v : Fin d → ℂ, (Qop H c g)ᴴ *ᵥ v = Pop c g *ᵥ v + Complex.I • (H *ᵥ v) := by
    intro v; rw [hQ, Matrix.add_mulVec, Matrix.smul_mulVec]
  ext ψ
  simp only [Set.mem_setOf_eq, hact, hact0]
  set v := WithLp.ofLp ψ
  constructor
  · rintro ⟨lam, hlam⟩
    rw [hQv] at hlam
    have hd := congrArg (fun w => star v ⬝ᵥ w) hlam
    simp only [dotProduct_add, dotProduct_smul, hPv, dotProduct_sum,
      hdot, smul_eq_mul] at hd
    have hre := congrArg Complex.re hd
    have hN : (star v ⬝ᵥ v).im = 0 := (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).2.symm
    have hA : ∀ l, 0 ≤ (star (c l *ᵥ v) ⬝ᵥ (c l *ᵥ v)).re ∧
        (star (c l *ᵥ v) ⬝ᵥ (c l *ᵥ v)).im = 0 := fun l =>
      ⟨(Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1,
       (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).2.symm⟩
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_sum, hBreal v, hN, zero_mul, mul_zero, sub_zero, zero_sub,
      one_mul, neg_zero, add_zero, Complex.mul_im] at hre
    have hsum : ∑ l, g l * (star (c l *ᵥ v) ⬝ᵥ (c l *ᵥ v)).re = 0 := by
      rw [← hre]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hg l).le (hA l).1)).mp hsum
    have hcv : ∀ l, c l *ᵥ v = 0 := by
      intro l
      have h0 := hz l (Finset.mem_univ l)
      have hre0 : (star (c l *ᵥ v) ⬝ᵥ (c l *ᵥ v)).re = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h (hg l).ne'
        · exact h
      apply dotProduct_star_self_eq_zero.mp
      exact Complex.ext hre0 (hA l).2
    refine ⟨hcv, lam, ?_⟩
    have hP0 : Pop c g *ᵥ v = 0 := by
      rw [hPv]; apply Finset.sum_eq_zero; intro l _; rw [hcv l, Matrix.mulVec_zero, smul_zero]
    rw [hP0, zero_add] at hlam
    have := congrArg (fun w => (-Complex.I) • w) hlam
    simp only [smul_smul] at this
    have e1 : -Complex.I * Complex.I = 1 := by simp
    have e2 : -Complex.I * (Complex.I * (lam : ℂ)) = (lam : ℂ) := by
      rw [← mul_assoc, e1, one_mul]
    rwa [e1, e2, one_smul] at this
  · rintro ⟨hcv, E, hE⟩
    refine ⟨E, ?_⟩
    have hP0 : Pop c g *ᵥ v = 0 := by
      rw [hPv]; apply Finset.sum_eq_zero; intro l _; rw [hcv l, Matrix.mulVec_zero, smul_zero]
    rw [hQv, hP0, zero_add, hE, smul_smul]
