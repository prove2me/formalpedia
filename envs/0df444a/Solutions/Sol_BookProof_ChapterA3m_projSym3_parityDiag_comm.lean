-- Prove2me | solution 1 for BookProof.ChapterA3m.projSym3_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:54:46.662023+00:00
-- url     : https://prove2.me/submissions/bf550846-22b3-44b8-8247-4a96994e2ae5

import Mathlib
import Definitions.Def_ChapterA3m
open Matrix
open scoped Kronecker
open BookProof.ChapterA3 BookProof.ChapterA3k BookProof.ChapterA3l BookProof.ChapterA3m

private def trans23 : Equiv.Perm ((Fin 4 × Fin 4) × Fin 4) where
  toFun a := ((a.1.1, a.2), a.1.2)
  invFun a := ((a.1.1, a.2), a.1.2)
  left_inv a := by rcases a with ⟨⟨a,b⟩,c⟩; rfl
  right_inv a := by rcases a with ⟨⟨a,b⟩,c⟩; rfl

private def trans13 : Equiv.Perm ((Fin 4 × Fin 4) × Fin 4) where
  toFun a := ((a.2, a.1.2), a.1.1)
  invFun a := ((a.2, a.1.2), a.1.1)
  left_inv a := by rcases a with ⟨⟨a,b⟩,c⟩; rfl
  right_inv a := by rcases a with ⟨⟨a,b⟩,c⟩; rfl

-- Identify the supplied swaps as permutation operators. No products are expanded.
private lemma swap_perm : BookProof.ChapterA3l.swap =
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 4) (Fin 4)) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [BookProof.ChapterA3l.swap, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Prod.ext_iff, eq_comm, and_comm]

private lemma swap23_perm : swap23 = trans23.permMatrix ℂ := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩
  simp [swap23, trans23, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Prod.ext_iff, eq_comm, and_assoc]

private lemma swap13_perm : swap13 = trans13.permMatrix ℂ := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩
  simp [swap13, trans13, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Prod.ext_iff, eq_comm, and_assoc]

-- The permutation-matrix formulas turn braiding into reindexing of tensor slots.
-- These identities hold for arbitrary equal factors, independently of gamma entries.
private lemma equal_pair_swap (A : Matrix (Fin 4) (Fin 4) ℂ) :
    BookProof.ChapterA3l.swap * (A ⊗ₖ A) = (A ⊗ₖ A) * BookProof.ChapterA3l.swap := by
  rw [swap_perm, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  exact Matrix.ext fun ⟨a,b⟩ ⟨c,d⟩ => mul_comm _ _

private lemma equal_triple_swap12 (A : Matrix (Fin 4) (Fin 4) ℂ) :
    swap12 * ((A ⊗ₖ A) ⊗ₖ A) = ((A ⊗ₖ A) ⊗ₖ A) * swap12 := by
  rw [swap12, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, equal_pair_swap]

private lemma equal_triple_swap23 (A : Matrix (Fin 4) (Fin 4) ℂ) :
    swap23 * ((A ⊗ₖ A) ⊗ₖ A) = ((A ⊗ₖ A) ⊗ₖ A) * swap23 := by
  rw [swap23_perm, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  exact Matrix.ext fun ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩ => mul_right_comm _ _ _

private lemma equal_triple_swap13 (A : Matrix (Fin 4) (Fin 4) ℂ) :
    swap13 * ((A ⊗ₖ A) ⊗ₖ A) = ((A ⊗ₖ A) ⊗ₖ A) * swap13 := by
  rw [swap13_perm, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  exact Matrix.ext fun ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩ => by
    change (A c d * A b e) * A a f = (A a f * A b e) * A c d
    ac_rfl

theorem solution : projSym3 * parityDiag3 = parityDiag3 * projSym3 := by
  have h12 : Commute swap12 parityDiag3 := equal_triple_swap12 (mgamma 0)
  have h23 : Commute swap23 parityDiag3 := equal_triple_swap23 (mgamma 0)
  have h13 : Commute swap13 parityDiag3 := equal_triple_swap13 (mgamma 0)
  have hsum := ((((Commute.one_left parityDiag3).add_left h12).add_left h23).add_left
    (h12.mul_left h23)).add_left (h23.mul_left h12) |>.add_left h13
  simpa only [projSym3, Matrix.smul_mul, Matrix.mul_smul] using
    congrArg (fun T : M3 => (6 : ℂ)⁻¹ • T) hsum.eq

#print axioms solution
