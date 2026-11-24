-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exceptional_zero_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:10.140232+00:00
-- url     : https://prove2.me/submissions/3820037b-c107-4907-8adb-f6b61bb9c6b9

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (x A q cE β : ℝ) (hx : 2 ≤ x) (hA : 0 < A) (hq : 1 ≤ q)
    (hqL : q ≤ Real.log x ^ A) (hcE : 0 < cE) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β ≤ 1 - cE * q ^ (-(1 / (2 * A)))) :
    ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hn : ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ = x ^ β / β := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.ofReal_re, Complex.norm_real,
      Real.norm_of_nonneg hβ0.le]
  rw [hn]
  have hq0 : (0:ℝ) < q := by linarith
  have hA0 : A ≠ 0 := hA.ne'
  have h1 : q ^ (1 / (2 * A)) ≤ Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow]
    calc q ^ (1 / (2 * A)) ≤ (Real.log x ^ A) ^ (1 / (2 * A)) :=
          Real.rpow_le_rpow hq0.le hqL (by positivity)
      _ = Real.log x ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hlog.le]
          congr 1
          field_simp
  have h2 : q ^ (-(1 / (2 * A))) = (q ^ (1 / (2 * A)))⁻¹ := Real.rpow_neg hq0.le _
  have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hlog
  have hqa : 0 < q ^ (1 / (2 * A)) := Real.rpow_pos_of_pos hq0 _
  have h3 : cE / Real.sqrt (Real.log x) ≤ 1 - β := by
    have h3a : cE * q ^ (-(1 / (2 * A))) ≤ 1 - β := by linarith
    rw [h2] at h3a
    calc cE / Real.sqrt (Real.log x) ≤ cE / q ^ (1 / (2 * A)) :=
          div_le_div_of_nonneg_left hcE.le hqa h1
      _ = cE * (q ^ (1 / (2 * A)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1 - β := h3a
  have h4 : (β - 1) * Real.log x ≤ -cE * Real.sqrt (Real.log x) := by
    have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x := Real.mul_self_sqrt hlog.le
    have h4a := (div_le_iff₀ hs).mp h3
    nlinarith
  have h5 : x ^ β ≤ x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
    have e1 : x * Real.exp (-cE * Real.sqrt (Real.log x)) =
        Real.exp (Real.log x + -cE * Real.sqrt (Real.log x)) := by
      rw [Real.exp_add, Real.exp_log hx0]
    rw [e1, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h6 : x ^ β / β ≤ 2 * x ^ β := by
    rw [div_le_iff₀ hβ0]
    have h6a := Real.rpow_pos_of_pos hx0 β
    nlinarith
  linarith [h5, h6]
end Formalism.ZeroFreeDirichlet
