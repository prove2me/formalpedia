-- Prove2me | solution 1 for CauchyRiemannIndex.fundamentalSolution_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:15:49.638368+00:00
-- url     : https://prove2.me/submissions/7930d992-5287-4671-800a-dc44ac23d93b

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed

open Matrix

namespace CauchyRiemannIndex

lemma crj_fund_existsUnique (n : ℕ) (S : ℝ → Mat n) (hS : Continuous S) :
    ∃! Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let A : ℝ → Mat n := fun t => J₀ n * S t
  have hA : Continuous A := continuous_const.mul hS
  let B : ℝ → Mat n →L[ℝ] Mat n :=
    fun t => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (A t))
  have hB : Continuous B := by
    refine continuous_clm_apply.2 fun y => ?_
    exact hA.mul continuous_const
  obtain ⟨Ψ, ⟨hΨ0, hΨ⟩, huniq⟩ := AsymptoticOperator.linearODE_existsUnique B hB 1
  exact ⟨Ψ, ⟨hΨ0, hΨ⟩, fun Φ hΦ => huniq Φ ⟨hΦ.1, hΦ.2⟩⟩

lemma crj_fund_symplectic (n : ℕ) (S : ℝ → Mat n) (hS : ∀ t, (S t).IsSymm)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) (t : ℝ) : IsSymplectic (Ψ t) := by
  obtain ⟨hΨ0, hd⟩ := hΨ
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let T : Mat n →L[ℝ] Mat n :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) ℝ ℝ).toLinearMap
  have hT : ∀ s : ℝ, HasDerivAt (fun s => (Ψ s)ᵀ) ((J₀ n * S s * Ψ s)ᵀ) s :=
    fun s => T.hasFDerivAt.comp_hasDerivAt s (hd s)
  have hJ : ∀ X : Mat n, J₀ n * (J₀ n * X) = -X := by
    intro X
    rw [← mul_assoc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, neg_one_mul]
  have hf : ∀ s : ℝ, HasDerivAt (fun s => (Ψ s)ᵀ * J₀ n * Ψ s) 0 s := by
    intro s
    have h := ((hT s).mul_const (J₀ n)).mul (hd s)
    have hsym : (S s)ᵀ = S s := hS s
    have key : (J₀ n * S s * Ψ s)ᵀ * J₀ n * Ψ s +
        (Ψ s)ᵀ * J₀ n * (J₀ n * S s * Ψ s) = 0 := by
      rw [transpose_mul, transpose_mul, hsym, show (J₀ n)ᵀ = -J₀ n from Matrix.J_transpose _ _]
      simp only [mul_assoc, neg_mul, mul_neg, hJ]
      simp
    rw [key] at h
    exact h
  have hc : (Ψ t)ᵀ * J₀ n * Ψ t = J₀ n := by
    have := is_const_of_deriv_eq_zero (f := fun s => (Ψ s)ᵀ * J₀ n * Ψ s)
      (fun x => (hf x).differentiableAt) (fun x => (hf x).deriv) t 0
    rw [this]
    simp [hΨ0]
  have hmem : (Ψ t)ᵀ ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    rw [SymplecticGroup.mem_iff, transpose_transpose]
    exact hc
  exact SymplecticGroup.transpose_mem_iff.1 hmem

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (S : ℝ → Mat n) (hS : ∀ t, (S t).IsSymm)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) (t : ℝ) : IsSymplectic (Ψ t) :=
  crj_fund_symplectic n S hS Ψ hΨ t
