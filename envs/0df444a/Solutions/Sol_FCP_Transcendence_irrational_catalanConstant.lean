-- Prove2me | solution 1 for FCP.Transcendence.irrational_catalanConstant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:31:06.817392+00:00
-- url     : https://prove2.me/submissions/fd124ada-41e5-400d-ac44-8265a495bccc

import Mathlib
import Definitions.Def_FCP_CatalanConstant
import Theorems.Thm_OAI_InternalCatalan_catalan_irrational

/-! Catalan's constant is irrational: `FCP.Constants.catalanConstant` is the series of
OpenAI's statement `OAI.InternalCatalan.catalan_irrational`, with the denominator written
without the cast from `ℕ`. -/

theorem fcp_catalanConstant_eq_oai_series :
    FCP.Constants.catalanConstant =
      ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  unfold FCP.Constants.catalanConstant
  push_cast
  rfl

theorem solution : Irrational FCP.Constants.catalanConstant := by
  rw [fcp_catalanConstant_eq_oai_series]
  exact OAI.InternalCatalan.catalan_irrational
