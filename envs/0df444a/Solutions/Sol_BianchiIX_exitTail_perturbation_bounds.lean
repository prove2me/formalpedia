-- Prove2me | solution 1 for BianchiIX.exitTail_perturbation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:56:05.248868+00:00
-- url     : https://prove2.me/submissions/773ac58e-c8af-4291-9188-6954c29a72b9

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

end
end

private theorem BianchiIX.exitTail_rate_differences {R u v w : ℝ}
    (ht : exitTailGap R v ≠ 0) (hd : exitTailSpeed R u v w ≠ 0) :
    exitTailStrongRate R u v w - exitTailStrongRate R 0 v 0 =
      (2 * v * w - w ^ 2 + u ^ 2 - 2 * coupling u v w * exitTailStrongRate R 0 v 0) /
        (2 * exitTailSpeed R u v w) ∧
    exitTailWeakRate R u v w - exitTailWeakRate R 0 v 0 =
      -coupling u v w * (1 + exitTailWeakRate R 0 v 0) / exitTailSpeed R u v w := by
  have hs : exitTailSpeed R 0 v 0 = exitTailGap R v := by simp [exitTailSpeed, coupling]
  simp only [exitTailStrongRate, exitTailWeakRate, hs, coupling, zero_mul, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero]
  constructor <;> field_simp <;> dsimp only [exitTailSpeed, coupling] <;> ring

private theorem BianchiIX.exitTail_boundary_rate_bounds {R v : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hv : 0 ≤ v ∧ v ≤ 1) :
    |exitTailStrongRate R 0 v 0| ≤ 20 ∧ |exitTailWeakRate R 0 v 0| ≤ 7 := by
  obtain ⟨ht, htR⟩ := exitTailGap_compact hR.1 hv
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hR2 : R ^ 2 ≤ 25 := by nlinarith only [hR.1, hR.2]
  have hs : exitTailSpeed R 0 v 0 = exitTailGap R v := by simp [exitTailSpeed, coupling]
  simp only [exitTailStrongRate, exitTailWeakRate, hs, coupling, zero_mul, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero, abs_div,
    abs_of_pos ht0, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht0)]
  constructor
  · apply (div_le_iff₀ (mul_pos (by norm_num) ht0)).mpr
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (mul_nonneg (by norm_num) ht0.le), abs_of_nonneg (sq_nonneg R)]
    nlinarith only [hR2, ht]
  · apply (div_le_iff₀ ht0).mpr
    apply (abs_sub _ _).trans
    rw [abs_of_pos ht0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [ht]


/-- Signed-wall perturbations preserve the vanishing orders needed for the long terminal tail. -/
theorem solution {R u v w : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hu : |u| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    |exitTailRadial R u v w| ≤ 20 * (|u| * v + (|u| + |w|) ^ 2) ∧
    |exitTailStrongRate R u v w - exitTailStrongRate R 0 v 0| ≤
      100 * ((|u| + |w|) * v + (|u| + |w|) ^ 2) ∧
    |exitTailWeakRate R u v w - exitTailWeakRate R 0 v 0| ≤
      100 * ((|u| + |w|) * v + (|u| + |w|) ^ 2) := by
  let b := |u| + |w|
  let H := b * v + b ^ 2
  have hb : 0 ≤ b := add_nonneg (abs_nonneg u) (abs_nonneg w)
  have hH : 0 ≤ H := add_nonneg (mul_nonneg hb hv.1) (sq_nonneg b)
  obtain ⟨ht, htR⟩ := exitTailGap_compact hR.1 hv
  have ht0 : 0 < exitTailGap R v := by linarith only [ht]
  have hR0 : 0 < R := by linarith only [hR.1]
  have hd := exitTailSpeed_compact hR.1 hu hv hw
  have hd0 : 0 < exitTailSpeed R u v w := by linarith only [hd]
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have hcH : |coupling u v w| ≤ H := by
    have H' := mul_nonneg (abs_nonneg w) hv.1
    dsimp only [H, b]
    nlinarith only [hc, H']
  have hsq : (u - w) ^ 2 ≤ b ^ 2 := by
    have H' := abs_sub u w
    nlinarith only [H', sq_abs (u - w), abs_nonneg (u - w), hb]
  have hsum : |2 * v * w - w ^ 2 + u ^ 2| ≤ 2 * H := by
    have H' := (abs_add_le (2 * v * w - w ^ 2) (u ^ 2)).trans
      (add_le_add (abs_sub (2 * v * w) (w ^ 2)) le_rfl)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hv.1, abs_of_nonneg (sq_nonneg w), abs_of_nonneg (sq_nonneg u)] at H'
    have Huv := mul_nonneg (abs_nonneg u) hv.1
    have Huw := mul_nonneg (abs_nonneg u) (abs_nonneg w)
    dsimp only [H, b]
    nlinarith only [H', Huv, Huw, sq_abs u, sq_abs w, sq_nonneg |u|, sq_nonneg |w|]
  obtain ⟨hU, hW⟩ := exitTail_boundary_rate_bounds hR hv
  obtain ⟨dU, dW⟩ := exitTail_rate_differences (ne_of_gt ht0) (ne_of_gt hd0)
  refine ⟨?_, ?_, ?_⟩
  · rw [exitTailRadial, abs_div, abs_of_pos hd0]
    apply (div_le_iff₀ hd0).mpr
    have H' := abs_sub (-coupling u v w * R) (exitTailGap R v * (u - w) ^ 2 / R)
    rw [abs_mul, abs_neg, abs_of_pos hR0,
      abs_of_nonneg (div_nonneg (mul_nonneg ht0.le (sq_nonneg _)) hR0.le)] at H'
    have hquot : exitTailGap R v * (u - w) ^ 2 / R ≤ b ^ 2 := by
      apply (div_le_iff₀ hR0).mpr
      exact (mul_le_mul_of_nonneg_right htR (sq_nonneg _)).trans
        (by nlinarith only [mul_le_mul_of_nonneg_left hsq hR0.le])
    have hcoupled : |coupling u v w| * R ≤ 5 * (|u| * v + b ^ 2) := by
      have hR5 : R ≤ 5 := by linarith only [hR.2]
      have Hc := mul_le_mul hc hR5 hR0.le (add_nonneg (mul_nonneg (abs_nonneg u) hv.1) (sq_nonneg b))
      change _ ≤ (|u| * v + b ^ 2) * 5 at Hc
      linarith only [Hc]
    have hbase : 0 ≤ |u| * v + b ^ 2 := add_nonneg (mul_nonneg (abs_nonneg u) hv.1) (sq_nonneg b)
    have Hbudget := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hbase)
    nlinarith only [H', hquot, hcoupled, Hbudget, mul_nonneg (abs_nonneg u) hv.1]
  · rw [dU, abs_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd0)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hd0)).mpr
    have H' := abs_sub (2 * v * w - w ^ 2 + u ^ 2) (2 * coupling u v w * exitTailStrongRate R 0 v 0)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H'
    have Hprod := mul_le_mul hcH hU (abs_nonneg _) hH
    have Hbudget := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hH)
    change _ ≤ 100 * H * (2 * exitTailSpeed R u v w)
    nlinarith only [H', hsum, Hprod, Hbudget, hH]
  · rw [dW, abs_div, abs_of_pos hd0, abs_mul, abs_neg]
    apply (div_le_iff₀ hd0).mpr
    have H' : |1 + exitTailWeakRate R 0 v 0| ≤ 8 := by
      have H'' := abs_add_le (1 : ℝ) (exitTailWeakRate R 0 v 0)
      rw [abs_one] at H''
      linarith only [H'', hW]
    have Hprod := mul_le_mul hcH H' (abs_nonneg _) hH
    have Hbudget := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hH)
    change _ ≤ 100 * H * exitTailSpeed R u v w
    nlinarith only [Hprod, Hbudget, hH]
