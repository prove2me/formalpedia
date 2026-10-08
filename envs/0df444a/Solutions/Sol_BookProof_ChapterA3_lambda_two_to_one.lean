-- Prove2me | solution 1 for BookProof.ChapterA3.lambda_two_to_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:47:33.750383+00:00
-- url     : https://prove2.me/submissions/69bf8491-1781-4ac5-838f-773394ddf757

import Mathlib
import Definitions.Def_ChapterA3c
open Matrix BookProof.ChapterA3

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private lemma majorana_commutant (R : Matrix (Fin 4) (Fin 4) ℝ)
    (hR : ∀ μ, mgammaR μ * R = R * mgammaR μ) :
    R = R 0 0 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have h0 (i j : Fin 4) := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hR 0)
  have h1 (i j : Fin 4) := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hR 1)
  have h2 (i j : Fin 4) := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hR 2)
  have h3 (i j : Fin 4) := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hR 3)
  simp [mgammaR, mgammaZ, Matrix.mul_apply, Fin.sum_univ_succ] at h0 h1 h2 h3
  simp only [Fin.forall_fin_succ] at h0 h1 h2 h3
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.succ] at h0 h1 h2 h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> linarith!

private lemma lambda_witness {S : Matrix (Fin 4) (Fin 4) ℝ} (hS : IsPin S) :
    HasLambda S (LambdaOf S) := by
  classical
  simp only [LambdaOf, dif_pos hS.2.2]
  exact hS.2.2.choose_spec

theorem solution (hpf : PauliFundamental)
    {S S' : Matrix (Fin 4) (Fin 4) ℝ} (hS : IsPin S) (hS' : IsPin S')
    (h : LambdaOf S = LambdaOf S') : S' = S ∨ S' = -S := by
  have he (μ : Fin 4) : S⁻¹ * mgammaR μ * S = S'⁻¹ * mgammaR μ * S' := by
    rw [lambda_witness hS μ, lambda_witness hS' μ, h]
  have hi := Matrix.mul_nonsing_inv S hS.1
  have hi' := Matrix.mul_nonsing_inv S' hS'.1
  have hj' := Matrix.nonsing_inv_mul S' hS'.1
  have hc (μ : Fin 4) : mgammaR μ * (S * S'⁻¹) = (S * S'⁻¹) * mgammaR μ := by
    have hh := congrArg (fun A => S * A * S'⁻¹) (he μ)
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc S S⁻¹, hi,
      Matrix.one_mul, Matrix.mul_assoc, hi', Matrix.mul_one] using hh
  have hs := majorana_commutant (S * S'⁻¹) hc
  let c : ℝ := (S * S'⁻¹) 0 0
  have hsc : S = c • S' := by
    have hh := congrArg (fun A => A * S') hs
    simpa only [Matrix.mul_assoc, hj', Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] using hh
  have hd : |c| ^ 4 = 1 := by
    have hh := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => |A.det|) hsc
    simpa [Matrix.det_smul, abs_mul, abs_pow, hS.2.1, hS'.2.1] using hh.symm
  have hca : |c| = 1 := by nlinarith [abs_nonneg c, sq_nonneg (|c| ^ 2 - 1)]
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hca with hc1 | hc1
  · left
    simpa [hc1] using hsc.symm
  · right
    simpa [hc1] using congrArg Neg.neg hsc.symm

#print axioms solution
