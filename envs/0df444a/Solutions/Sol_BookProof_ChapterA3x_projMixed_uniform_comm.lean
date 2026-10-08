-- Prove2me | solution 1 for BookProof.ChapterA3x.projMixed_uniform_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:56:18.660082+00:00
-- url     : https://prove2.me/submissions/46980406-6900-4eb1-9403-b64adc5507e9

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_uniform_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

namespace LocalChapterA3n
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
end LocalChapterA3n

namespace LocalChapterA3o
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open LocalChapterA3n
theorem projAnti_uniform_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * uniform A = uniform A * projAnti N := by
  unfold projAnti
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, permMat_uniform_comm]
end LocalChapterA3o

open LocalChapterA3n LocalChapterA3o

theorem solution {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projMixed N * uniform A = uniform A * projMixed N := by
  simp only [projMixed, sub_mul, mul_sub, one_mul, mul_one,
    projSym_uniform_comm, projAnti_uniform_comm]

#print axioms solution
