-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_bound_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:24.652805+00:00
-- url     : https://prove2.me/submissions/e074eee8-cffb-470b-9abf-0b7cc726e525

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_mul_rpow_log_sq_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_pow_le_and_rho_le_of_log_bounds
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_rpow_nine_tenths_le

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
theorem _root_.solution : ExponentialRangeSizeConditions := by
  intro ε C C_B C₀ c Cρ c₃ hε hC hCB hC₀ hc hCρ hc₃
  set K : ℝ := Real.log (200 * Cρ) with hKdef
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_mul_rpow_log_sq_le_rpow ε (C₀ * C_B) hε).and ((eventually_mul_rpow_log_sq_le_rpow ε (|K| * C_B / c) hε).and
      ((eventually_le_rpow ε ((K / c) ^ 2) hε).and ((eventually_mul_rpow_log_sq_le_rpow ε (240 * C_B) hε).and
        ((eventually_le_rpow ε (40 * Real.log (40 / c₃)) hε).and (eventually_le_rpow ε 1 hε))))))
  refine ⟨x₀, fun x hx B Y hB hlB hY1 hY2 => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hx₀ x hx
  set β : ℝ := x ^ (ε / 5) * Real.log x ^ 2 with hβ
  set L : ℝ := x ^ ε with hL
  have hlB' : Real.log B ≤ C_B * β := by rw [hβ]; linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY1
  have hl8 : 8 * L ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).mpr hY1
  have hB0 : 0 < B := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos (by linarith)
  have hlY : 0 < Real.log Y := by linarith
  have k1 : C₀ * Real.log B ≤ Real.log Y := by
    have : C₀ * Real.log B ≤ C₀ * (C_B * β) := mul_le_mul_of_nonneg_left hlB' hC₀.le
    linarith
  have k2 : K * Real.log B ≤ c * Real.log Y := by
    have t1 : K * Real.log B ≤ |K| * Real.log B := mul_le_mul_of_nonneg_right (le_abs_self K) hlB0.le
    have t2 : |K| * Real.log B ≤ |K| * (C_B * β) := mul_le_mul_of_nonneg_left hlB' (abs_nonneg K)
    have t3 : c * (|K| * C_B / c * β) ≤ c * L := mul_le_mul_of_nonneg_left e2 hc.le
    have t4 : c * (|K| * C_B / c * β) = |K| * (C_B * β) := by field_simp
    have t5 : c * L ≤ c * Real.log Y := mul_le_mul_of_nonneg_left (by linarith) hc.le
    linarith
  have k3 : K ≤ c * Real.log Y ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have t1 : |K / c| ≤ Real.sqrt (Real.log Y) := Real.abs_le_sqrt (by linarith)
    have t2 : K / c ≤ Real.sqrt (Real.log Y) := le_trans (le_abs_self _) t1
    rw [div_le_iff₀ hc] at t2
    linarith
  have hKe : Cρ * Real.exp (-K) ≤ 1 / 200 := by
    rw [Real.exp_neg, hKdef, Real.exp_log (by positivity)]
    apply le_of_eq
    field_simp
  have k4 : 7 * Real.log B - Real.log 1 ≤ Real.log Y / 3 := by
    rw [Real.log_one]; linarith
  obtain ⟨r1, r2, r3⟩ := pow_le_and_rho_le_of_log_bounds C₀ c Cρ B Y 1 K hCρ hB hY0 one_pos k1 hKe k2 k3 k4
  exact ⟨r1, r2, r3, rpow_nine_tenths_le c₃ B Y hc₃ hB0 hY0 hlY (by linarith) (by linarith)⟩
end Formalism.HermitianLattices.ZeroFreeRegionGL2
