-- Prove2me | solution 1 for BookProof.WeylHamiltonian.smul_nonneg_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:31:15.990781+00:00
-- url     : https://prove2.me/submissions/f71a3577-36b5-490c-a1e3-211392f5759c

-- Generated from ChapterWeylHamiltonian.lean — theorem BookProof.WeylHamiltonian.smul_nonneg_isPositive
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
open BookProof.WeylHamiltonian



open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open BookProof.WeylHamiltonian

theorem solution(T : H →L[ℂ] H) (h : T.IsPositive)
    {c : ℝ} (hc : 0 ≤ c) : ((c : ℂ) • T).IsPositive := by
  first
  | exact h.smul_of_nonneg (Complex.zero_le_real.mpr hc)
  | exact h.smul_of_nonneg (by exact_mod_cast hc)
