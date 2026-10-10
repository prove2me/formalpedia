-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp74.prop74_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:45:59.825991+00:00
-- url     : https://prove2.me/submissions/124701c8-94ed-4e74-b875-51bbf0465362

-- Generated from ChapterMajoranaProp74.lean — solution of BookProof.ChapterMajoranaProp74.prop74_intertwine
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
    (hg2 : g * g = 1) (hns2 : ns * ns = -1) (hgns : g * ns = -(ns * g))
    (c s m q E : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hm : m = (c ^ 2 - s ^ 2) * E)
    (hq : q = 2 * c * s * E) :
    Qmat g ns m q * Sinv (ns * g) c s = Sinv (ns * g) c s * Rmat g E := by

      unfold Qmat Sinv Rmat;
      simp only [neg_smul, Complex.coe_smul, fromBlocks_multiply, Algebra.mul_smul_comm, mul_one,
          mul_neg, Algebra.smul_mul_assoc, ← Matrix.mul_assoc, smul_neg, neg_mul, one_mul, mul_zero,
              add_zero, zero_add, fromBlocks_inj];
      simp_all only [mul_comm, mul_left_comm, Complex.ofReal_mul, Complex.ofReal_sub,
          Complex.ofReal_pow, Complex.ofReal_ofNat, neg_mul, one_mul, smul_neg, neg_neg, mul_assoc,
              mul_one];
      refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> ext <;> norm_num <;> ring;
      · rw [ show ( s : ℂ ) ^ 2 = 1 - c ^ 2 by norm_cast; linarith ] ; ring;
      · rw [ show ( s : ℂ ) ^ 3 = s * s ^ 2 by ring, show ( s : ℂ ) ^ 2 = 1 - c ^ 2
                                               by norm_cast; linarith ] ; ring;
      · rw [ show ( s : ℂ ) ^ 3 = s * s ^ 2 by ring, show ( s : ℂ ) ^ 2 = 1 - c ^ 2
                                               by norm_cast; linarith ] ; ring;
      · rw [ show ( s : ℂ ) ^ 2 = 1 - c ^ 2 by norm_cast; linarith ] ; ring
