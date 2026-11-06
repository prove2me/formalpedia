-- Prove2me | solution 1 for BianchiIX.stableCorrectedPhase_coefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:24:34.094477+00:00
-- url     : https://prove2.me/submissions/e15f568e-758f-4893-bf22-f2df9bf5937b

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_pos {m w : ℝ} (hm : -1 < m) : 0 < stableWeakRadius m w :=
  phaseNorm_pos (by linarith : 0 < m + 1)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectionA_partial_fractions {m : ℝ} (hm : 1 < m) :
    stableCorrectionA m = (1 / (m - 1) + 1 / (m + 1)) / 2 ∧
      stableCorrectionADeriv m = -(1 / (m - 1) ^ 2 + 1 / (m + 1) ^ 2) / 2 ∧
      stableCorrectionASecond m = 1 / (m - 1) ^ 3 + 1 / (m + 1) ^ 3 := by
  have h1 : m - 1 ≠ 0 := by linarith
  have h2 : m + 1 ≠ 0 := by linarith
  have h3 : m ^ 2 - 1 ≠ 0 := by nlinarith
  dsimp [stableCorrectionA, stableCorrectionADeriv, stableCorrectionASecond]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrection_coefficients_bounds {m : ℝ} (hm : 2 ≤ m) :
    |stableCorrectionA m| ≤ 2 / (m + 1) ∧
      |stableCorrectionADeriv m| ≤ 5 / (m + 1) ^ 2 ∧
      |stableCorrectionASecond m| ≤ 28 / (m + 1) ^ 3 ∧
      |stableCorrectionC m| = 2 / (m + 1) ∧
      |stableCorrectionCDeriv m| = 2 / (m + 1) ^ 2 ∧
      |stableCorrectionCSecond m| = 4 / (m + 1) ^ 3 := by
  have hL : 0 < m + 1 := by linarith
  have hD : 0 < m - 1 := by linarith
  have hp (n : ℕ) : 1 / (m - 1) ^ n ≤ 3 ^ n / (m + 1) ^ n := by
    apply (div_le_div_iff₀ (pow_pos hD n) (pow_pos hL n)).mpr
    simpa only [one_mul, mul_pow] using
      pow_le_pow_left₀ hL.le (show m + 1 ≤ 3 * (m - 1) by linarith) n
  obtain ⟨h0, h1, h2⟩ := stableCorrectionA_partial_fractions (by linarith : 1 < m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, abs_of_nonneg (by positivity)]
    have H := hp 1
    norm_num only [pow_one] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · rw [h1, neg_div, abs_neg, abs_of_nonneg (by positivity)]
    have H := hp 2
    norm_num only [Nat.reducePow] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · rw [h2, abs_of_nonneg (by positivity)]
    have H := hp 3
    norm_num only [Nat.reducePow] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · simp [stableCorrectionC, abs_div, abs_of_pos hL]
  · rw [stableCorrectionCDeriv, abs_of_nonneg (by positivity)]
  · simp [stableCorrectionCSecond, abs_div, abs_of_pos hL]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_coefficient_bounds {m w : ℝ} (hm : -1 < m) :
    |(m + 1) / stableWeakRadius m w - 1| ≤ w ^ 2 / (m + 1) ^ 2 ∧
      |w / stableWeakRadius m w| ≤ |w| / (m + 1) ∧
      |w ^ 2 / stableWeakRadius m w ^ 3| ≤ w ^ 2 / (m + 1) ^ 3 ∧
      |-(m + 1) * w / stableWeakRadius m w ^ 3| ≤ |w| / (m + 1) ^ 2 ∧
      |(m + 1) ^ 2 / stableWeakRadius m w ^ 3| ≤ 1 / (m + 1) := by
  have hL : 0 < m + 1 := by linarith
  have hS := stableWeakRadius_pos (w := w) hm
  have hLS : m + 1 ≤ stableWeakRadius m w := phaseNorm_ge hL.le
  have h3 := pow_le_pow_left₀ hL.le hLS 3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have H := phaseNorm_ratio_defect (b := w) hL
    change 1 - (m + 1) / stableWeakRadius m w =
      w ^ 2 * (1 / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))) at H
    rw [abs_sub_comm, H, abs_of_nonneg (by positivity), mul_one_div]
    apply div_le_div_of_nonneg_left (sq_nonneg w) (pow_pos hL 2)
    have H0 := mul_le_mul hLS (show m + 1 ≤ stableWeakRadius m w + (m + 1) by linarith)
      hL.le hS.le
    nlinarith only [H0]
  · rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_left (abs_nonneg w) hL hLS
  · rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (sq_nonneg w) (pow_pos hL 3) h3
  · rw [abs_div, abs_mul, abs_neg, abs_of_pos hL, abs_of_pos (pow_pos hS 3)]
    calc
      _ ≤ (m + 1) * |w| / (m + 1) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3) h3
      _ = |w| / (m + 1) ^ 2 := by field_simp
  · rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (m + 1) ^ 2 / (m + 1) ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hL 3) h3
      _ = 1 / (m + 1) := by field_simp

end
end

theorem solution {m u w : ℝ} (hm : 2 ≤ m) :
    let b := |u| + |w|
    |stableCorrectedGradient m u w 0 - 1| ≤ 8 / (m + 1) ^ 2 * b ^ 2 ∧
      |stableCorrectedGradient m u w 1| ≤ 6 / (m + 1) * b ∧
      |stableCorrectedGradient m u w 2| ≤ 3 / (m + 1) * b ∧
      |w ^ 2 / stableWeakRadius m w ^ 3 + stableCorrectionASecond m * u ^ 2 +
        stableCorrectionCSecond m * u * w| ≤ 33 / (m + 1) ^ 3 * b ^ 2 ∧
      |2 * stableCorrectionADeriv m * u + stableCorrectionCDeriv m * w| ≤ 12 / (m + 1) ^ 2 * b ∧
      |-(m + 1) * w / stableWeakRadius m w ^ 3 + stableCorrectionCDeriv m * u| ≤ 3 / (m + 1) ^ 2 * b := by
  let b := |u| + |w|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : |u| ≤ b := le_add_of_nonneg_right (abs_nonneg w)
  have hw : |w| ≤ b := le_add_of_nonneg_left (abs_nonneg u)
  have hu2 : |u ^ 2| ≤ b ^ 2 := by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hw2 : w ^ 2 ≤ b ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg w) hw 2
  have huw : |u| * |w| ≤ b ^ 2 := by nlinarith only [mul_le_mul hu hw (abs_nonneg w) hb]
  have hL : 0 < m + 1 := by linarith
  obtain ⟨ha, ha1, ha2, hc, hc1, hc2⟩ := stableCorrection_coefficients_bounds hm
  obtain ⟨hs0, hs1, hs2, hs3, _⟩ := stableWeakRadius_coefficient_bounds (m := m) (w := w) (by linarith)
  have htri (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : stableCorrectedGradient m u w 0 - 1 =
        ((m + 1) / stableWeakRadius m w - 1) + stableCorrectionADeriv m * u ^ 2 + stableCorrectionCDeriv m * u * w := by
      dsimp [stableCorrectedGradient, stableCorrectionADeriv, stableCorrectionCDeriv]
      ring
    rw [heq]
    have H := htri ((m + 1) / stableWeakRadius m w - 1)
      (stableCorrectionADeriv m * u ^ 2) (stableCorrectionCDeriv m * u * w)
    have H0 := div_le_div_of_nonneg_right hw2 (show 0 ≤ (m + 1) ^ 2 by positivity)
    have H1 := mul_le_mul ha1 hu2 (abs_nonneg _) (by positivity : 0 ≤ 5 / (m + 1) ^ 2)
    have H2 := mul_le_mul hc1.le huw (mul_nonneg (abs_nonneg u) (abs_nonneg w)) (by positivity : 0 ≤ 2 / (m + 1) ^ 2)
    simp only [abs_mul, div_eq_mul_inv] at H H0 H1 H2 hs0 ⊢
    nlinarith only [H, H0, H1, H2, hs0]
  · have H := abs_add_le (2 * stableCorrectionA m * u) (stableCorrectionC m * w)
    have H1 := mul_le_mul ha hu (abs_nonneg u) (by positivity : 0 ≤ 2 / (m + 1))
    have H2 := mul_le_mul hc.le hw (abs_nonneg w) (by positivity : 0 ≤ 2 / (m + 1))
    dsimp [stableCorrectedGradient]
    norm_num [abs_mul] at H
    simp only [div_eq_mul_inv] at H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · have H := abs_add_le (w / stableWeakRadius m w) (stableCorrectionC m * u)
    have H1 := div_le_div_of_nonneg_right hw hL.le
    have H2 := mul_le_mul hc.le hu (abs_nonneg u) (by positivity : 0 ≤ 2 / (m + 1))
    dsimp [stableCorrectedGradient]
    simp only [abs_mul, div_eq_mul_inv] at H H1 H2 hs1 ⊢
    nlinarith only [H, H1, H2, hs1]
  · have H := htri (w ^ 2 / stableWeakRadius m w ^ 3)
      (stableCorrectionASecond m * u ^ 2) (stableCorrectionCSecond m * u * w)
    have H0 := div_le_div_of_nonneg_right hw2 (show 0 ≤ (m + 1) ^ 3 by positivity)
    have H1 := mul_le_mul ha2 hu2 (abs_nonneg _) (by positivity : 0 ≤ 28 / (m + 1) ^ 3)
    have H2 := mul_le_mul hc2.le huw (mul_nonneg (abs_nonneg u) (abs_nonneg w)) (by positivity : 0 ≤ 4 / (m + 1) ^ 3)
    simp only [abs_mul, div_eq_mul_inv] at H H0 H1 H2 hs2 ⊢
    nlinarith only [H, H0, H1, H2, hs2]
  · have H := abs_add_le (2 * stableCorrectionADeriv m * u) (stableCorrectionCDeriv m * w)
    have H1 := mul_le_mul ha1 hu (abs_nonneg u) (by positivity : 0 ≤ 5 / (m + 1) ^ 2)
    have H2 := mul_le_mul hc1.le hw (abs_nonneg w) (by positivity : 0 ≤ 2 / (m + 1) ^ 2)
    norm_num [abs_mul] at H
    simp only [div_eq_mul_inv] at H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · have H := abs_add_le (-(m + 1) * w / stableWeakRadius m w ^ 3) (stableCorrectionCDeriv m * u)
    have H1 := div_le_div_of_nonneg_right hw (show 0 ≤ (m + 1) ^ 2 by positivity)
    have H2 := mul_le_mul hc1.le hu (abs_nonneg u) (by positivity : 0 ≤ 2 / (m + 1) ^ 2)
    simp only [abs_mul, div_eq_mul_inv] at H H1 H2 hs3 ⊢
    nlinarith only [H, H1, H2, hs3]
