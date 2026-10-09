-- Prove2me | solution 1 for BookProof.ChapterA3.fixesTimeAxis_iff_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:51:46.888807+00:00
-- url     : https://prove2.me/submissions/962c9861-0fa9-4b88-99b4-e3408de41755

-- Generated from ChapterA4c.lean — solution of BookProof.ChapterA3.fixesTimeAxis_iff_unitary
import Mathlib
import Definitions.Def_ChapterA4c
import Theorems.Thm_BookProof_ChapterA3_pauliCoeff_one
import Theorems.Thm_BookProof_ChapterA3_upsilonC_timeCol
import Theorems.Thm_BookProof_ChapterA3_upsilon_re
import Theorems.Thm_BookProof_ChapterA3_pauli_expand
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) :
    FixesTimeAxis (Upsilon T) ↔ Tᴴ * T = 1 := by

  constructor
  · intro h
    have hcoeff : ∀ μ, pauliCoeff (Tᴴ * T) μ = if μ = 0 then 1 else 0 := by
      intro μ
      rw [← upsilonC_timeCol, ← upsilon_re]
      have := h μ
      rw [this]
      split <;> norm_num
    calc Tᴴ * T = ∑ μ, pauliCoeff (Tᴴ * T) μ • pauliσ μ := pauli_expand _
      _ = ∑ μ, (if μ = 0 then (1 : ℂ) else 0) • pauliσ μ := by
            apply Finset.sum_congr rfl; intro μ _; rw [hcoeff μ]
      _ = 1 := by
            simp only [ite_smul, one_smul, zero_smul]
            rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 4) (fun μ => pauliσ μ)]
            simp only [Finset.mem_univ, if_true]
            ext i j; fin_cases i <;> fin_cases j <;> simp [pauliσ]
  · intro h μ
    have hval : (Upsilon T μ 0 : ℂ) = if μ = 0 then 1 else 0 := by
      rw [upsilon_re, upsilonC_timeCol, h, pauliCoeff_one]
    have hre := congrArg Complex.re hval
    simp only [Complex.ofReal_re] at hre
    rw [hre]
    split <;> simp
