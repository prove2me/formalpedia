-- Prove2me | solution 1 for BookProof.ChapterA3q.projMixed_diagGen_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:05:31.870982+00:00
-- url     : https://prove2.me/submissions/597d0d58-7445-4b79-b1b0-bfd3bcbc1fbf

import Definitions.Def_ChapterA3q
import Mathlib
set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3n
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem permMat_braiding {N : ℕ} (σ : Equiv.Perm (Fin N))
    (M : Fin N → Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat σ := by
  ext a c;
  simp only [permMat, tensorPow, mul_apply, of_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply, Equiv.Perm.coe_inv,
          mul_ite, mul_one, mul_zero];
  rw [ Finset.sum_eq_single ( c ∘ σ.symm ) ];
  · conv_rhs => rw [ ← Equiv.prod_comp σ ] ;
    grind;
  · intro b _ hb; contrapose! hb; aesop;
  · exact fun h => False.elim <| h <| Finset.mem_univ _

theorem permMat_diagGen_comm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * diagGen A = diagGen A * permMat σ := by
  unfold diagGen
  rw [Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp σ (fun i => tensorPow (fun j => if j = i then A else 1) * permMat σ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [permMat_braiding]
  refine congrArg (· * permMat σ) (congrArg tensorPow (funext fun j => ?_))
  simp only [Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem projSym_diagGen_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projSym N * diagGen A = diagGen A * projSym N := by
  unfold projSym;
  simp only [smul_mul_assoc, mul_smul_comm];
  simp only [Finset.sum_mul, permMat_diagGen_comm, Finset.mul_sum _ _ _]
end BookProof.ChapterA3n

namespace BookProof.ChapterA3o
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem projAnti_diagGen_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * diagGen A = diagGen A * projAnti N := by
  unfold projAnti
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, permMat_diagGen_comm]
end BookProof.ChapterA3o

open BookProof.ChapterA3 BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q

theorem solution {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projMixed N * diagGen A = diagGen A * projMixed N := by
  unfold projMixed
  simp only [sub_mul, mul_sub, one_mul, mul_one,
    projSym_diagGen_comm, projAnti_diagGen_comm]

#print axioms solution
