-- Prove2me | solution 1 for BlackScholesModel.stdNormalPDF_dPlus_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:26:29.622+00:00
-- url     : https://prove2.me/submissions/cf818f7d-97d5-438b-9936-671feea6b949

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_pdf_dPlus_dMinus_balance

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
open BlackScholesModel

theorem solution
    (S K r σ τ : ℝ) (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    S * stdNormalPDF (dPlus S K r σ τ) =
      K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ) := by
  apply BlackScholesModel.pdf_dPlus_dMinus_balance <;> assumption


