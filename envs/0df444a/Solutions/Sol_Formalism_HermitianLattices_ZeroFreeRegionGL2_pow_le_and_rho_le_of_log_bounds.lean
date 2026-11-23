-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.pow_le_and_rho_le_of_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:55.595347+00:00
-- url     : https://prove2.me/submissions/a0b50901-c558-4007-8ac8-cd428ebd6751

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution (C₀ c Cρ B X h K : ℝ) (hCρ : 0 < Cρ) (hB : 4 ≤ B) (hX : 0 < X) (hh : 0 < h)
    (h1 : C₀ * Real.log B ≤ Real.log X)
    (hK : Cρ * Real.exp (-K) ≤ h / 200)
    (h2 : K * Real.log B ≤ c * Real.log X)
    (h3 : K ≤ c * Real.log X ^ (1 / 2 : ℝ))
    (h4 : 7 * Real.log B - Real.log h ≤ Real.log X / 3) :
    B ^ C₀ ≤ X ∧ rho c Cρ B X ≤ h / 100 ∧ B ^ 7 ≤ h * X ^ (1 / 3 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hB0]
    calc Real.exp (Real.log B * C₀) ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by linarith)
      _ = X := Real.exp_log hX
  · unfold rho
    have e1 : Real.exp (-c * Real.log X / Real.log B) ≤ Real.exp (-K) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ hlB]
      linarith
    have e2 : Real.exp (-c * Real.log X ^ (1 / 2 : ℝ)) ≤ Real.exp (-K) := by
      apply Real.exp_le_exp.mpr
      linarith
    have e3 := mul_le_mul_of_nonneg_left e1 hCρ.le
    have e4 := mul_le_mul_of_nonneg_left e2 hCρ.le
    linarith
  · have p7 : Real.exp (7 * Real.log B) = B ^ 7 := by
      have := Real.exp_nat_mul (Real.log B) 7
      rw [Real.exp_log hB0] at this
      simpa using this
    rw [← p7, Real.rpow_def_of_pos hX]
    calc Real.exp (7 * Real.log B) ≤ Real.exp (Real.log h + Real.log X * (1 / 3)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = h * Real.exp (Real.log X * (1 / 3)) := by rw [Real.exp_add, Real.exp_log hh]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
