-- Prove2me | solution 1 for BoundEntGauss.S_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T14:58:27.250957+00:00
-- url     : https://prove2.me/submissions/5b94ce76-a1c3-49d1-a448-07e11dacac1a

import Mathlib
import Definitions.Def_BoundEntGauss_totalSigma
import Definitions.Def_BoundEntGauss_sigmaTilde
import Definitions.Def_BoundEntGauss_opS

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open BoundEntGauss QAlgorithms.Papers.Independent.Intakenext100.P68 in
theorem solution :
    opS * totalSigma 2 2 + sigmaTilde 2 2 * opS = 0 ∧
    ∀ Γ : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2) (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ,
      opS * Γ = Γ * opS →
      complexify Γ - Complex.I • complexify (sigmaTilde 2 2) =
        complexify opS * (complexify Γ + Complex.I • complexify (totalSigma 2 2)) * complexify opS := by
  have h1 : opS * totalSigma 2 2 + sigmaTilde 2 2 * opS = 0 := by
    ext i j
    simp only [opS, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases j with ⟨c, d⟩ | ⟨c, d⟩ <;>
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [totalSigma, sigmaTilde, realCovarianceSum, interleavedJ]
  have hSS : opS * opS = 1 := by
    unfold opS
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> fin_cases a <;> fin_cases b <;> simp
  refine ⟨h1, fun Γ hΓ => ?_⟩
  have hSΓS : opS * Γ * opS = Γ := by rw [hΓ, mul_assoc, hSS, mul_one]
  have hSσ : opS * totalSigma 2 2 = -(sigmaTilde 2 2 * opS) := eq_neg_of_add_eq_zero_left h1
  have hSσS : opS * totalSigma 2 2 * opS = -sigmaTilde 2 2 := by
    rw [hSσ, neg_mul, mul_assoc, hSS, mul_one]
  have hc : ∀ A : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2)
      (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ, complexify A = A.map Complex.ofRealHom := by
    intro A; ext i j; rfl
  rw [hc, hc, hc, hc]
  have e1 : opS.map Complex.ofRealHom * Γ.map Complex.ofRealHom * opS.map Complex.ofRealHom =
      Γ.map Complex.ofRealHom := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hSΓS]
  have e2 : opS.map Complex.ofRealHom * (totalSigma 2 2).map Complex.ofRealHom *
      opS.map Complex.ofRealHom = -(sigmaTilde 2 2).map Complex.ofRealHom := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hSσS, Matrix.map_neg _ (fun a => map_neg _ a)]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, e2, smul_neg,
    sub_eq_add_neg]
