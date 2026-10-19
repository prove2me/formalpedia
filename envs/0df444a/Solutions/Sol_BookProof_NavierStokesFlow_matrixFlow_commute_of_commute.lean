-- Prove2me | solution 1 for BookProof.NavierStokesFlow.matrixFlow_commute_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:51:42.459697+00:00
-- url     : https://prove2.me/submissions/c58e8a07-2e08-447b-85c6-bb0fe19838d1

import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_commute_of_commute
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)
theorem h43_mf_deriv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (matrixFlow A) (matrixFlow A t * A) t := by
  unfold matrixFlow
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) A t

theorem h43_mf_deriv' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (matrixFlow A) (A * matrixFlow A t) t := by
  unfold matrixFlow
  exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t

theorem h43_mf_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    matrixFlow A (s + t) = matrixFlow A s * matrixFlow A t := by
  unfold matrixFlow
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s |>.smul_right t)

theorem h43_mf_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : matrixFlow A 0 = 1 := by
  unfold matrixFlow; simp

theorem h43_mf_mul_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    matrixFlow A t * matrixFlow A (-t) = 1 := by
  rw [← h43_mf_add]; simp [h43_mf_zero]

theorem h43_mf_comm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    matrixFlow A t * A = A * matrixFlow A t := by
  unfold matrixFlow
  exact ((Commute.refl A).smul_left t).exp_left.eq

theorem h43_ns_eq {n : ℕ} (d : NSTruncation n) (t : ℝ) :
    nsFlowUnitary d t = matrixFlow (Complex.I • nsHamiltonian d) t := by
  unfold nsFlowUnitary matrixFlow
  congr 1
  rw [mul_smul, Complex.coe_smul]

theorem h43_mf_neg_deriv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matrixFlow A (-s)) (-(matrixFlow A (-t) * A)) t := by
  have h := (h43_mf_deriv A (-t)).scomp t (hasDerivAt_neg t)
  simp only [Function.comp_def, neg_mul, one_smul, neg_smul] at h
  exact h

theorem h43_mf_vec_deriv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matrixFlow A s *ᵥ x) (A *ᵥ (matrixFlow A t *ᵥ x)) t := by
  have h := (applyVecCLM x).hasFDerivAt.comp_hasDerivAt t (h43_mf_deriv' A t)
  have e : applyVecCLM x (A * matrixFlow A t) = A *ᵥ (matrixFlow A t *ᵥ x) := by
    simp [applyVecCLM, Matrix.mulVec_mulVec]
  exact h.congr_deriv e

theorem h43_mf_unique {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (y : ℝ → Fin n → ℂ)
    (hy : ∀ t, HasDerivAt y (A *ᵥ y t) t) (hy0 : y 0 = x) (t : ℝ) :
    y t = matrixFlow A t *ᵥ x := by
  have hz : ∀ s, HasDerivAt (fun s => matrixFlow A (-s) *ᵥ y s) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => mulVecCLM' (matrixFlow A (-s)))
        (mulVecCLM' (-(matrixFlow A (-s) * A))) s :=
      mulVecCLM'.hasFDerivAt.comp_hasDerivAt s (h43_mf_neg_deriv A s)
    have h2 := h1.clm_apply (hy s)
    have e : (mulVecCLM' (-(matrixFlow A (-s) * A))) (y s) + (mulVecCLM' (matrixFlow A (-s))) (A *ᵥ y s) = 0 := by
      simp [mulVecCLM', mulVecCLM, Matrix.mulVec_mulVec, Matrix.neg_mulVec]
    rw [e] at h2
    simpa [mulVecCLM', mulVecCLM] using h2
  have hc := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt) (fun s => (hz s).deriv) t 0
  simp only [neg_zero, h43_mf_zero, Matrix.one_mulVec, hy0] at hc
  have := congrArg (fun v => matrixFlow A t *ᵥ v) hc
  simp only [Matrix.mulVec_mulVec] at this
  rw [h43_mf_mul_neg, Matrix.one_mulVec] at this
  exact this

theorem h43_mf_cauchy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ∃! y : ℝ → Fin n → ℂ, y 0 = x ∧ ∀ t, HasDerivAt y (A *ᵥ y t) t := by
  refine ⟨fun s => matrixFlow A s *ᵥ x, ⟨by simp [h43_mf_zero], fun t => h43_mf_vec_deriv A x t⟩, ?_⟩
  rintro y ⟨hy0, hy⟩
  funext t
  exact h43_mf_unique A x y hy hy0 t

theorem h43_ns_eq_fun {n : ℕ} (d : NSTruncation n) :
    nsFlowUnitary d = matrixFlow (Complex.I • nsHamiltonian d) := funext (h43_ns_eq d)

theorem h43_ns_comm {n : ℕ} (d : NSTruncation n) (t : ℝ) :
    nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t := by
  unfold nsFlowUnitary
  exact ((Commute.refl (nsHamiltonian d)).smul_left _).exp_left.eq

theorem h43_ns_herm {n : ℕ} (d : NSTruncation n) : (nsHamiltonian d)ᴴ = nsHamiltonian d := by
  have hA : ∀ i, (nsAdvection d i)ᴴ = nsAdvection d i := by
    intro i
    simp only [nsAdvection, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, nsVelocity, nsGradVelocity,
      nsLapVelocity, d.u_herm, Complex.star_def, Complex.conj_ofReal]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => d.u_comm _ _)
  simp only [nsHamiltonian, Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hA, d.mom_herm]
  exact Finset.sum_congr rfl (fun i _ => add_comm _ _)

theorem h43_ns_adj {n : ℕ} (d : NSTruncation n) (t : ℝ) :
    (nsFlowUnitary d t)ᴴ = nsFlowUnitary d (-t) := by
  unfold nsFlowUnitary
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h43_ns_herm]
  congr 2
  simp [Complex.star_def]

theorem h43_ns_unitary {n : ℕ} (d : NSTruncation n) (t : ℝ) :
    (nsFlowUnitary d t)ᴴ * nsFlowUnitary d t = 1 := by
  rw [h43_ns_adj, h43_ns_eq, h43_ns_eq, ← h43_mf_add]; simp [h43_mf_zero]

theorem h43_energy {n : ℕ} (d : NSTruncation n) (t : ℝ) (psi : Fin n → ℂ) :
    star (nsFlowUnitary d t *ᵥ psi) ⬝ᵥ (nsHamiltonian d *ᵥ (nsFlowUnitary d t *ᵥ psi))
      = star psi ⬝ᵥ (nsHamiltonian d *ᵥ psi) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, ← h43_ns_comm, ← Matrix.mul_assoc, h43_ns_unitary, Matrix.one_mul]

theorem solution (t : ℝ) :
    nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t := by
  exact h43_ns_comm d t

