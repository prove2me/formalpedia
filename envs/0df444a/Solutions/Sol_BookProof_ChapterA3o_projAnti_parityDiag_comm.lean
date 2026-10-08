-- Prove2me | solution 1 for BookProof.ChapterA3o.projAnti_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:20:01.165848+00:00
-- url     : https://prove2.me/submissions/36ca1b1f-1e2e-444f-adb4-37f83c121b64

-- Generated from ChapterA3o.lean — theorem BookProof.ChapterA3o.projAnti_parityDiag_comm
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3
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
private theorem local_uniform {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * uniform A = uniform A * permMat σ := by
  simpa only [uniform] using local_braiding σ (fun _ => A)

private theorem local_anti_uniform {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * uniform A = uniform A * projAnti N := by
  unfold projAnti
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, local_uniform]

theorem solution {N : ℕ} :
    projAnti N * uniform (mgamma 0) = uniform (mgamma 0) * projAnti N := by
  exact local_anti_uniform (mgamma 0)

#print axioms solution
