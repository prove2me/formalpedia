-- Prove2me | solution 1 for BookProof.ChapterA3x.projMixed_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:19:01.434021+00:00
-- url     : https://prove2.me/submissions/5cdd0dc0-7ab0-406e-9b01-2533e89b21bd

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3j
open BookProof.ChapterA3n
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

namespace LocalDiagonal
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
  simp only [Finset.mul_sum, Finset.sum_mul, permMat_braiding]
  have h : (fun i : Fin N => tensorPow (fun j => if σ⁻¹ j = i then A else 1) * permMat σ)
      = (fun i : Fin N => tensorPow (fun j => if j = σ i then A else 1) * permMat σ) := by
    funext i
    have hf : (fun j : Fin N => if σ⁻¹ j = i then A else 1) =
        (fun j : Fin N => if j = σ i then A else 1) := by
      funext j
      change (if σ.symm j = i then A else 1) = _
      simp only [σ.symm_apply_eq]
    rw [hf]
  rw [h]
  exact Equiv.sum_comp σ (fun i => tensorPow (fun j => if j = i then A else 1) * permMat σ)

theorem sym_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    BookProof.ChapterA3n.projSym N * diagGen A = diagGen A * BookProof.ChapterA3n.projSym N := by
  unfold BookProof.ChapterA3n.projSym
  simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
    permMat_diagGen_comm]

theorem anti_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * diagGen A = diagGen A * projAnti N := by
  unfold projAnti
  simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
    permMat_diagGen_comm]

theorem mixed_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projMixed N * diagGen A = diagGen A * projMixed N := by
  simp only [projMixed, sub_mul, mul_sub, one_mul, mul_one, sym_comm, anti_comm]
end LocalDiagonal

theorem solution {N : ℕ} (μ ν : Fin 4) :
    projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N := by
  exact LocalDiagonal.mixed_comm (spinGen μ ν)

#print axioms solution
