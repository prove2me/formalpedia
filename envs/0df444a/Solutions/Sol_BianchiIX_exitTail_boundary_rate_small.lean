-- Prove2me | solution 1 for BianchiIX.exitTail_boundary_rate_small
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:56:01.723207+00:00
-- url     : https://prove2.me/submissions/2677c6f0-6be4-4586-b350-e331ece9ed4c

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_boundary_rates {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 < R ^ 2) :
    exitTailStrongRate R 0 v 0 = -(R - 2) / 2 - R * v ^ 2 / (2 * exitTailGap R v * (R + exitTailGap R v)) ∧
    exitTailWeakRate R 0 v 0 = (R - 2) / R - 2 * v ^ 2 / (R * exitTailGap R v * (R + exitTailGap R v)) := by
  have ht : 0 < exitTailGap R v := Real.sqrt_pos.mpr (sub_pos.mpr hv)
  have hs := exitTailGap_sq hv.le
  have hp : R + exitTailGap R v ≠ 0 := ne_of_gt (add_pos hR ht)
  simp only [exitTailStrongRate, exitTailWeakRate, exitTailSpeed, coupling, zero_mul,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero]
  constructor <;> field_simp <;> nlinarith only [hs, congrArg (R * ·) hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end


/-- The boundary rates are integrably small: alpha plus radial drift plus V squared. -/
theorem solution {R v α : ℝ} (hα : 0 ≤ α)
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hv : 0 ≤ v ∧ v ≤ 1) :
    |exitTailStrongRate R 0 v 0| + |exitTailWeakRate R 0 v 0| ≤
      10 * (α + |R - (2 + 2 * α)| + v ^ 2) := by
  obtain ⟨ht, htR⟩ := exitTailGap_compact hR.1 hv
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hR1 : 1 ≤ R := by linarith only [hR.1]
  have hR0 : 0 < R := by linarith only [hR1]
  have htv : v ^ 2 < R ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  obtain ⟨hU, hW⟩ := exitTail_boundary_rates hR0 htv
  have hsum : 1 ≤ R + exitTailGap R v := by linarith only [ht, hR1]
  have hdu : 1 ≤ 2 * exitTailGap R v * (R + exitTailGap R v) := by
    have H := mul_le_mul ht hsum (by norm_num : (0 : ℝ) ≤ 1) ht0.le
    nlinarith only [H]
  have hrt : 1 ≤ R * exitTailGap R v := by
    nlinarith only [mul_le_mul hR1 ht (by norm_num : (0 : ℝ) ≤ 1) hR0.le]
  have hdw : 1 ≤ R * exitTailGap R v * (R + exitTailGap R v) := by
    nlinarith only [mul_le_mul hrt hsum (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hR0.le ht0.le)]
  have hdu0 : 0 < 2 * exitTailGap R v * (R + exitTailGap R v) := by linarith only [hdu]
  have hdw0 : 0 < R * exitTailGap R v * (R + exitTailGap R v) := by linarith only [hdw]
  have huq : R * v ^ 2 / (2 * exitTailGap R v * (R + exitTailGap R v)) ≤ 5 * v ^ 2 := by
    apply (div_le_iff₀ hdu0).mpr
    have H := mul_le_mul_of_nonneg_left hdu (by positivity : 0 ≤ 5 * v ^ 2)
    have H' := mul_le_mul_of_nonneg_right hR.2 (sq_nonneg v)
    nlinarith only [H, H', sq_nonneg v]
  have hwq : 2 * v ^ 2 / (R * exitTailGap R v * (R + exitTailGap R v)) ≤ 2 * v ^ 2 := by
    apply (div_le_iff₀ hdw0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hdw (by positivity : 0 ≤ 2 * v ^ 2)]
  have hUabs : |exitTailStrongRate R 0 v 0| ≤ |R - 2| / 2 + 5 * v ^ 2 := by
    rw [hU]
    have H := abs_sub (-(R - 2) / 2) (R * v ^ 2 / (2 * exitTailGap R v * (R + exitTailGap R v)))
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (div_nonneg (mul_nonneg hR0.le (sq_nonneg v)) hdu0.le)] at H
    linarith only [H, huq]
  have hWabs : |exitTailWeakRate R 0 v 0| ≤ |R - 2| + 2 * v ^ 2 := by
    rw [hW]
    have H := abs_sub ((R - 2) / R) (2 * v ^ 2 / (R * exitTailGap R v * (R + exitTailGap R v)))
    rw [abs_div, abs_of_pos hR0,
      abs_of_nonneg (div_nonneg (by positivity : 0 ≤ 2 * v ^ 2) hdw0.le)] at H
    have Hq : |R - 2| / R ≤ |R - 2| := (div_le_iff₀ hR0).mpr
      (by nlinarith only [mul_le_mul_of_nonneg_left hR1 (abs_nonneg (R - 2))])
    linarith only [H, Hq, hwq]
  have herr : |R - 2| ≤ |R - (2 + 2 * α)| + 2 * α := by
    have H := abs_add_le (R - (2 + 2 * α)) (2 * α)
    rw [show R - (2 + 2 * α) + 2 * α = R - 2 by ring,
      abs_of_nonneg (mul_nonneg (by norm_num) hα)] at H
    exact H
  linarith only [hUabs, hWabs, herr, hα, abs_nonneg (R - (2 + 2 * α)), sq_nonneg v]
