-- Prove2me | solution 1 for BookProof.ChapterA3q.projMixed_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:05:11.589465+00:00
-- url     : https://prove2.me/submissions/ec1b8c52-25f1-40cc-b78c-843c6d00d2b9

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

theorem permMat_uniform_comm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * uniform A = uniform A * permMat σ := by
  simpa only [uniform] using permMat_braiding σ (fun _ => A)

theorem projSym_uniform_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projSym N * uniform A = uniform A * projSym N := by
  unfold projSym;
  simp only [smul_mul_assoc, mul_smul_comm];
  simp only [Finset.sum_mul, permMat_uniform_comm, Finset.mul_sum _ _ _]
end BookProof.ChapterA3n

namespace BookProof.ChapterA3o
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem projAnti_uniform_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * uniform A = uniform A * projAnti N := by
  unfold projAnti
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, permMat_uniform_comm]
end BookProof.ChapterA3o

open BookProof.ChapterA3 BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q

theorem solution {N : ℕ} :
    projMixed N * uniform (mgamma 0) = uniform (mgamma 0) * projMixed N := by
  unfold projMixed
  simp only [sub_mul, mul_sub, one_mul, mul_one, projSym_uniform_comm, projAnti_uniform_comm]

#print axioms solution
