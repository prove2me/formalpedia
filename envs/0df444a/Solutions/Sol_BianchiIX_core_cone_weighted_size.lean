-- Prove2me | solution 1 for BianchiIX.core_cone_weighted_size
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:27:48.174854+00:00
-- url     : https://prove2.me/submissions/25354e75-f5bd-4102-a555-ec33c15799a0

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- Small entrance walls control the weighted size of every unit radial cone direction. -/
theorem solution {k ε u w a b : ℝ} (hk : 6 ≤ k)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w) :
    let Q := 1 + k * |a| + |b|
    Real.sqrt u * Q ≤ 3 * Real.sqrt ε ∧ Real.sqrt w * Q ≤ 3 * Real.sqrt ε ∧
      Real.sqrt u + (u + w) * Q ≤ 7 * Real.sqrt ε := by
  intro Q
  have hk0 : 0 < k := by linarith only [hk]
  have hue : u ≤ ε := hu.2.trans (div_le_self hε.1 (by linarith only [hk]))
  have hwe : w ≤ ε := hw.2.trans (div_le_self hε.1 (by linarith only [hk]))
  have hsu := Real.sqrt_le_sqrt hue
  have hsw := Real.sqrt_le_sqrt hwe
  have hsu0 := Real.sqrt_nonneg u
  have hsw0 := Real.sqrt_nonneg w
  have hse0 := Real.sqrt_nonneg ε
  have hsu2 := Real.sq_sqrt hu.1
  have hsw2 := Real.sq_sqrt hw.1
  have hse2 := Real.sq_sqrt hε.1
  have hse1 : Real.sqrt ε ≤ 1 := by nlinarith only [hse0, hse2, hε.2]
  have hes : ε ≤ Real.sqrt ε := by nlinarith only [hse0, hse1, hse2]
  have hku : k * u ≤ ε := by simpa only [mul_comm] using (le_div_iff₀ hk0).mp hu.2
  have hkw : k * w ≤ ε := by simpa only [mul_comm] using (le_div_iff₀ hk0).mp hw.2
  have hcross : Real.sqrt u * Real.sqrt w ≤ ε / k := by
    nlinarith only [hsu2, hsw2, hu.2, hw.2, sq_nonneg (Real.sqrt u - Real.sqrt w)]
  have hkcross : k * (Real.sqrt u * Real.sqrt w) ≤ ε := by
    simpa only [mul_comm] using (le_div_iff₀ hk0).mp hcross
  have hcross' : Real.sqrt u * Real.sqrt w ≤ ε :=
    hcross.trans (div_le_self hε.1 (by linarith only [hk]))
  have hQ : Q ≤ 1 + k * Real.sqrt u + Real.sqrt w := by
    dsimp [Q]
    nlinarith only [mul_le_mul_of_nonneg_left ha hk0.le, hb]
  have huQ : Real.sqrt u * Q ≤ 3 * Real.sqrt ε := by
    have H := mul_le_mul_of_nonneg_left hQ hsu0
    have heq : Real.sqrt u * (1 + k * Real.sqrt u + Real.sqrt w) =
        Real.sqrt u + k * u + Real.sqrt u * Real.sqrt w := by
      calc
        _ = Real.sqrt u + k * (Real.sqrt u) ^ 2 + Real.sqrt u * Real.sqrt w := by ring
        _ = _ := by rw [hsu2]
    rw [heq] at H
    nlinarith only [H, hsu, hku, hcross', hes]
  have hwQ : Real.sqrt w * Q ≤ 3 * Real.sqrt ε := by
    have H := mul_le_mul_of_nonneg_left hQ hsw0
    nlinarith only [H, hsw, hsw2, hkcross, hwe, hes]
  refine ⟨huQ, hwQ, ?_⟩
  have H := mul_le_mul_of_nonneg_left huQ hsu0
  have H' := mul_le_mul_of_nonneg_left hwQ hsw0
  have hU : u * Q ≤ 3 * ε := by
    calc
      _ = Real.sqrt u * (Real.sqrt u * Q) := by rw [← mul_assoc, Real.mul_self_sqrt hu.1]
      _ ≤ Real.sqrt u * (3 * Real.sqrt ε) := H
      _ ≤ Real.sqrt ε * (3 * Real.sqrt ε) := mul_le_mul_of_nonneg_right hsu (by positivity)
      _ = 3 * ε := by nlinarith only [hse2]
  have hW : w * Q ≤ 3 * ε := by
    calc
      _ = Real.sqrt w * (Real.sqrt w * Q) := by rw [← mul_assoc, Real.mul_self_sqrt hw.1]
      _ ≤ Real.sqrt w * (3 * Real.sqrt ε) := H'
      _ ≤ Real.sqrt ε * (3 * Real.sqrt ε) := mul_le_mul_of_nonneg_right hsw (by positivity)
      _ = 3 * ε := by nlinarith only [hse2]
  nlinarith only [hsu, hU, hW, hes]
