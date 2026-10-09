-- Prove2me | solution 1 for BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:12:39.421166+00:00
-- url     : https://prove2.me/submissions/b388f90c-6236-4b3d-9fed-86e5ba4bba7d

-- Generated from ChapterFiniteArithmeticPrior.lean — solution of BookProof.ChapterFiniteArithmeticPrior.truncMul_extension_consistent
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
import Theorems.Thm_BookProof_ChapterFiniteArithmeticPrior_truncMul_eq_mul
open BookProof.ChapterFiniteArithmeticPrior

set_option maxHeartbeats 1000000 in
theorem solution {B : ℕ} [NeZero B] {H : Type*} [Fintype H]
    (E : BayesianArithmeticExtension B H) (hE : E.known = truncMul B)
    (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) :
    ((E.known.result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ) ∧
      (∀ x, 0 ≤ E.prior x) ∧ ∑ x, E.prior x = 1 := by

  refine ⟨?_, E.prior_nonneg, E.prior_sum_one⟩
  rw [hE]
  exact truncMul_eq_mul a b h
