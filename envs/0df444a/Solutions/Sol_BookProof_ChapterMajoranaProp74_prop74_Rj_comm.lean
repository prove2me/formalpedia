-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp74.prop74_Rj_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:46:03.689018+00:00
-- url     : https://prove2.me/submissions/2358534d-24a1-4384-8877-b1992c4d4ecc

-- Generated from ChapterMajoranaProp74.lean — solution of BookProof.ChapterMajoranaProp74.prop74_Rj_comm
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaProp74



open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (g ns : Matrix (Fin 4) (Fin 4) ℂ)
    (_hg2 : g * g = 1) (hgns : g * ns = -(ns * g)) (c s pj : ℝ) :
    Dmat g pj * Sinv (ns * g) c s = Sinv (ns * g) c s * Dmat g pj := by

      unfold Dmat Sinv;
      simp only [neg_smul, Complex.coe_smul, fromBlocks_multiply, Algebra.mul_smul_comm, mul_one,
          mul_neg, zero_mul, smul_zero, neg_zero, add_zero, Algebra.smul_mul_assoc, neg_mul,
              smul_neg, neg_neg, zero_add, one_mul, mul_zero, Matrix.mul_assoc, fromBlocks_inj,
                  neg_inj, and_self_left];
      simp only [← smul_assoc, Complex.real_smul, ← mul_assoc, hgns, neg_mul, smul_neg, neg_inj];
      exact ⟨ by ext; simp [ mul_assoc, mul_left_comm ], by ext; simp [ mul_assoc, mul_left_comm ],
                                                            by ext; simp [ mul_assoc, mul_left_comm
                                                                ] ⟩
