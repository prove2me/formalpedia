-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.first_estimate_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:14.180854+00:00
-- url     : https://prove2.me/submissions/c98022d0-5597-49c2-88fe-2426c6e8082f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow_mul_log_sq
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_bound_first
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_log_four_mul_mul_sq
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_four_le_four_mul_sq

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
theorem _root_.solution : PrimeEstimateOfIntervalHyp := by
  intro C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hInt ε C hε hC
  obtain ⟨x₁, hx₁⟩ := numerical_bound_first ε C 6 C₀ c Cρ c₃ hε hC (by norm_num) hC₀ hc hCρ hc₃
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp (eventually_le_rpow_mul_log_sq ε (Real.log 4) hε)
  refine ⟨max x₁ x₂, fun x hx d NE k Y hd hd4 hdX hNE hlNE hk hY1 hY2 => ?_⟩
  have e1 := hx₂ x (le_trans (le_max_right _ _) hx)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.one_lt.le
  have hN1 : (1 : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hNE
  have hld : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log (by linarith) hdX
    rwa [X2, Real.log_exp] at this
  have hlB : Real.log (4 * (d : ℝ) * (NE : ℝ) ^ 2) ≤ 6 * x ^ (ε / 5) * Real.log x ^ 2 := by
    rw [log_four_mul_mul_sq _ _ (by linarith) (by linarith)]
    linarith
  have hYlo : Real.exp (8 * x ^ ε) ≤ Y := by
    have p8 : Real.exp (8 * x ^ ε) = Real.exp (x ^ ε) ^ 8 := by
      have := Real.exp_nat_mul (x ^ ε) 8
      simpa using this
    rw [p8]
    refine le_trans (pow_le_pow_left₀ (Real.exp_pos _).le ?_ 8) hY1
    exact le_mul_of_one_le_left (Real.exp_pos _).le hk
  have hYhi : Y ≤ Real.exp (C * x ^ ε) := by
    rw [mul_comm, Real.exp_mul]; exact hY2
  obtain ⟨r1, r2, r3, r4⟩ := hx₁ x (le_trans (le_max_left _ _) hx) (4 * (d : ℝ) * (NE : ℝ) ^ 2) Y
    (four_le_four_mul_sq _ _ hd1 hN1) hlB hYlo hYhi
  have := hInt d NE Y 1 hd hd4 hNE r1 r2 one_pos le_rfl r3
  have h2 : Y * (1 + 1) = 2 * Y := by ring
  rw [h2] at this
  exact le_trans r4 this
end Formalism.HermitianLattices.ZeroFreeRegionGL2
