-- Prove2me | solution 1 for BookProof.ChapterA3o.projAnti_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:20:06.996097+00:00
-- url     : https://prove2.me/submissions/15bd1d8e-1672-4d82-aba2-7f2fad5def16

-- Generated from ChapterA3o.lean — theorem BookProof.ChapterA3o.projAnti_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3j
open BookProof.ChapterA3n
open BookProof.ChapterA3o


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n

private theorem local_braiding {N : ℕ} (σ : Equiv.Perm (Fin N))
    (M : Fin N → Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat σ := by
  ext a c
  simp only [permMat, tensorPow, mul_apply, of_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply, Equiv.Perm.coe_inv,
      mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (c ∘ σ.symm)]
  · conv_rhs => rw [← Equiv.prod_comp σ]
    grind
  · intro b _ hb
    contrapose! hb
    aesop
  · exact fun h => False.elim <| h <| Finset.mem_univ _
private theorem local_diag {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * diagGen A = diagGen A * permMat σ := by
  have hf (i : Fin N) :
      (fun j => if σ⁻¹ j = i then A else 1) =
      (fun j => if j = σ i then A else 1) := by
    funext j
    have h : σ⁻¹ j = i ↔ j = σ i := by
      constructor
      · intro h
        simpa using congrArg σ h
      · intro h
        simp [h]
    simp only [h]
  unfold diagGen
  simp only [Finset.mul_sum, local_braiding, hf]
  exact Equiv.sum_comp σ (fun i =>
    tensorPow (fun j => if j = i then A else 1) * permMat σ) |>.trans
      (Finset.sum_mul _ _ _).symm

private theorem local_anti_diag {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * diagGen A = diagGen A * projAnti N := by
  unfold projAnti
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, local_diag]

theorem solution {N : ℕ} (μ ν : Fin 4) :
    projAnti N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projAnti N := by
  exact local_anti_diag (spinGen μ ν)

#print axioms solution
