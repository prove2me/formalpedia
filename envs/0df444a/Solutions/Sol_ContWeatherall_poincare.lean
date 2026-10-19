-- Prove2me | solution 1 for ContWeatherall.poincare
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:49:16.563348+00:00
-- url     : https://prove2.me/submissions/288e11be-bf89-42b8-b288-0148812ce041

import Theorems.Thm_ContWeatherall_homotopy_formula
import Theorems.Thm_ContWeatherall_homotopyOp_contDiff

open CategoryTheory ContinuousAlternatingMap ContWeatherall
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}
    {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) (hclosed : extDeriv w = 0) :
    ∃ η : E → E [⋀^Fin k]→L[ℝ] F, ContDiff ℝ ∞ η ∧ extDeriv η = w := by
  refine ⟨homotopyOp w, homotopyOp_contDiff hw, ?_⟩
  have h := homotopy_formula hw
  have hz : homotopyOp (0 : E → E [⋀^Fin (k + 1 + 1)]→L[ℝ] F) = 0 := by
    funext x
    simp [homotopyOp]
  simpa only [hclosed, hz, add_zero] using h
