-- Prove2me | solution 1 for BianchiIX.matchingPhase_auxiliary_m_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:34:39.698681+00:00
-- url     : https://prove2.me/submissions/fd8027e6-ce3a-4b6a-8502-8f356bd7abaa

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingKernelDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

private theorem BianchiIX.phaseNormKernel_derivative_bounds {l a b : ℝ} (hl : 0 < l) (ha : l ≤ a) :
    0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 1 / (2 * l ^ 2) ∧
      |phaseNormKernelDa a b| ≤ 1 / l ^ 3 ∧
      |b * phaseNormKernelDb a b| ≤ 3 * b ^ 2 / (4 * l ^ 4) := by
  have ha0 : 0 < a := hl.trans_le ha
  have hK := phaseNorm_pos (b := b) ha0
  have hKa := phaseNorm_ge (b := b) ha0.le
  have hKl := ha.trans hKa
  have hSl : 2 * l ≤ phaseNorm a b + a := by linarith only [ha, hKl]
  have hS : 0 < phaseNorm a b + a := add_pos hK ha0
  have hprod : 2 * l ^ 2 ≤ phaseNorm a b * (phaseNorm a b + a) := by
    have H := mul_le_mul hKl hSl (by positivity : 0 ≤ 2 * l) hK.le
    nlinarith only [H]
  have hprod2 : 4 * l ^ 4 ≤ phaseNorm a b ^ 2 * (phaseNorm a b + a) ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * l ^ 2) hprod 2
    nlinarith only [H]
  refine ⟨by unfold phaseNormKernel; positivity, ?_, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hprod
  · rw [phaseNormKernelDa, abs_div, abs_neg, abs_one, abs_of_pos (pow_pos hK 3)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hKl 3)
  · have hid : |b * phaseNormKernelDb a b| =
        b ^ 2 * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2) := by
      have H : b * phaseNormKernelDb a b =
          -(b ^ 2 * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2)) := by
        dsimp [phaseNormKernelDb]
        ring
      rw [H, abs_neg, abs_of_nonneg (by positivity)]
    rw [hid]
    calc
      _ ≤ (b ^ 2 * (3 * phaseNorm a b)) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [hKa]) (sq_nonneg b)
      _ = 3 * b ^ 2 / (phaseNorm a b ^ 2 * (phaseNorm a b + a) ^ 2) := by field_simp
      _ ≤ 3 * b ^ 2 / (4 * l ^ 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hprod2

end
end

theorem solution {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    0 ≤ matchingPhaseSlopeDm m v w ∧
    matchingPhaseSlopeDm m v w ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) ∧
    |matchingPhaseWeightDm m v w - 1| ≤ 3 * (v ^ 2 + w ^ 2) / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have ha0 : 0 < m + 1 := by linarith only [hμ, (abs_le.mp hm).1]
  have hb0 : 0 < m - 1 := by linarith only [hμ, (abs_le.mp hm).1]
  have hp0 := phaseNorm_pos (b := v) ha0
  have hn0 := phaseNorm_pos (b := w) hb0
  have wall (a b : ℝ) (ha : 5 * μ / 8 ≤ a) :
      0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 3 / (2 * μ ^ 2) ∧
        b ^ 2 / phaseNorm a b ^ 3 ≤ 9 * b ^ 2 / (2 * μ ^ 3) := by
    have ha0' : 0 < a := by linarith only [ha, hμ0]
    have hK := phaseNorm_pos (b := b) ha0'
    have H := phaseNormKernel_derivative_bounds (b := b) (by positivity : 0 < 5 * μ / 8) ha
    refine ⟨H.1, H.2.1.trans ?_, ?_⟩
    · convert! div_le_div_of_nonneg_right (show (32 / 25 : ℝ) ≤ 3 / 2 by norm_num) (sq_nonneg μ) using 1 <;> ring
    · have Hcube : 1 / phaseNorm a b ^ 3 ≤ 9 / (2 * μ ^ 3) := by
        have Hda := H.2.2.1
        rw [phaseNormKernelDa, abs_div, abs_neg, abs_one, abs_of_pos (pow_pos hK 3)] at Hda
        apply Hda.trans
        convert! div_le_div_of_nonneg_right (show (512 / 125 : ℝ) ≤ 9 / 2 by norm_num)
          (by positivity : 0 ≤ μ ^ 3) using 1 <;> ring
      convert! mul_le_mul_of_nonneg_left Hcube (sq_nonneg b) using 1 <;> ring
  have hp := wall (m + 1) v (by linarith only [hμ, (abs_le.mp hm).1])
  have hn := wall (m - 1) w (by linarith only [hμ, (abs_le.mp hm).1])
  have hqpos : 0 ≤ v ^ 2 / phaseNorm (m + 1) v ^ 3 := by positivity
  have hrpos : 0 ≤ w ^ 2 / phaseNorm (m - 1) w ^ 3 := by positivity
  have hfm : matchingPhaseSlopeDm m v w ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) :=
    (add_le_add hp.2.2 hn.2.2).trans_eq (by ring)
  have hf : |matchingPhaseSlope m v w - 1| ≤ 3 * (v ^ 2 + w ^ 2) / (2 * μ ^ 2) := by
    have hpR := phaseNorm_ratio_defect (b := v) ha0
    have hnR := phaseNorm_ratio_defect (b := w) hb0
    have hid : matchingPhaseSlope m v w - 1 =
        -(v ^ 2 * phaseNormKernel (m + 1) v + w ^ 2 * phaseNormKernel (m - 1) w) := by
      dsimp [matchingPhaseSlope]
      linarith only [hpR, hnR]
    rw [hid, abs_neg, abs_of_nonneg (add_nonneg (mul_nonneg (sq_nonneg v) hp.1) (mul_nonneg (sq_nonneg w) hn.1))]
    exact (add_le_add (mul_le_mul_of_nonneg_left hp.2.1 (sq_nonneg v))
      (mul_le_mul_of_nonneg_left hn.2.1 (sq_nonneg w))).trans_eq (by ring)
  refine ⟨add_nonneg hqpos hrpos, hfm, ?_⟩
  have hid : matchingPhaseWeightDm m v w - 1 =
      (matchingPhaseSlope m v w - 1) - v ^ 2 / phaseNorm (m + 1) v ^ 3 + w ^ 2 / phaseNorm (m - 1) w ^ 3 := by
    dsimp [matchingPhaseWeightDm]
    ring
  rw [hid]
  have H := (abs_add_le (matchingPhaseSlope m v w - 1 - v ^ 2 / phaseNorm (m + 1) v ^ 3)
    (w ^ 2 / phaseNorm (m - 1) w ^ 3)).trans
      (add_le_add (abs_sub (matchingPhaseSlope m v w - 1) (v ^ 2 / phaseNorm (m + 1) v ^ 3)) le_rfl)
  rw [abs_of_nonneg hqpos, abs_of_nonneg hrpos] at H
  calc
    _ ≤ |matchingPhaseSlope m v w - 1| + matchingPhaseSlopeDm m v w := H.trans_eq (by dsimp [matchingPhaseSlopeDm]; ring)
    _ ≤ 3 * (v ^ 2 + w ^ 2) / (2 * μ ^ 2) + 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := add_le_add hf hfm
    _ = (3 * μ + 9) * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := by field_simp
    _ ≤ 6 * μ * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith only [hμ]) (by positivity)
    _ = 3 * (v ^ 2 + w ^ 2) / μ ^ 2 := by field_simp; ring
