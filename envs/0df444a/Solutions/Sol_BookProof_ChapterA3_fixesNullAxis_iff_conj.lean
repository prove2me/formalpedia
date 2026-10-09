-- Prove2me | solution 1 for BookProof.ChapterA3.fixesNullAxis_iff_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:52:29.57261+00:00
-- url     : https://prove2.me/submissions/2cfbaf2c-b609-4fe6-8744-b76449fe9a1a

-- Generated from ChapterA4d.lean — solution of BookProof.ChapterA3.fixesNullAxis_iff_conj
import Mathlib
import Definitions.Def_ChapterA4d
import Theorems.Thm_BookProof_ChapterA3_pauliCoeff_null
import Theorems.Thm_BookProof_ChapterA3_upsilonC_nullCol
import Theorems.Thm_BookProof_ChapterA3_pauli_expand
import Theorems.Thm_BookProof_ChapterA3_upsilon_re
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) :
    FixesNullAxis (Upsilon T) ↔ Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3 := by

  constructor
  · intro h
    have hcoeff : ∀ μ, pauliCoeff (Tᴴ * (pauliσ 0 + pauliσ 3) * T) μ =
        (if μ = 0 then (1:ℂ) else 0) + (if μ = 3 then 1 else 0) := by
      intro μ
      rw [← upsilonC_nullCol]
      have h0 := (upsilon_re T μ 0).symm
      have h3 := (upsilon_re T μ 3).symm
      rw [h0, h3, ← Complex.ofReal_add, h μ]
      split_ifs <;> push_cast <;> ring
    calc Tᴴ * (pauliσ 0 + pauliσ 3) * T
          = ∑ μ, pauliCoeff (Tᴴ * (pauliσ 0 + pauliσ 3) * T) μ • pauliσ μ :=
            pauli_expand _
      _ = ∑ μ, pauliCoeff (pauliσ 0 + pauliσ 3) μ • pauliσ μ := by
            apply Finset.sum_congr rfl; intro μ _; rw [hcoeff μ, pauliCoeff_null μ]
      _ = pauliσ 0 + pauliσ 3 := (pauli_expand _).symm
  · intro h μ
    have hval : (Upsilon T μ 0 : ℂ) + (Upsilon T μ 3 : ℂ) =
        (if μ = 0 then (1:ℂ) else 0) + (if μ = 3 then 1 else 0) := by
      rw [upsilon_re, upsilon_re, upsilonC_nullCol, h, pauliCoeff_null]
    have hre := congrArg Complex.re hval
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    rw [hre]
    split <;> split <;> norm_num
