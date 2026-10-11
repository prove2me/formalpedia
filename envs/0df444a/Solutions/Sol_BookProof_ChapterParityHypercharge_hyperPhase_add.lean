-- Prove2me | solution 1 for BookProof.ChapterParityHypercharge.hyperPhase_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:57.696021+00:00
-- url     : https://prove2.me/submissions/c7221fc3-4538-4fb5-a45a-12155c4d3cbf

-- Generated from ChapterParityHypercharge.lean — solution of BookProof.ChapterParityHypercharge.hyperPhase_add
import Mathlib
import Definitions.Def_ChapterParityHypercharge
import Theorems.Thm_BookProof_ChapterA3_mgamma5_sq
import Definitions.Def_ChapterA3
open BookProof.ChapterParityHypercharge



open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (θ φ : ℝ) :
    hyperPhase θ * hyperPhase φ = hyperPhase (θ + φ) := by

  unfold hyperPhase
  simp only [Complex.ofReal_cos, Complex.ofReal_sin, mul_add, Algebra.mul_smul_comm, mul_one,
    smul_add, smul_smul, add_mul, Algebra.smul_mul_assoc, one_mul, Real.cos_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Real.sin_add, Complex.ofReal_add, add_smul]
  rw [BookProof.ChapterA3.mgamma5_sq]
  ext i j; norm_num; ring
