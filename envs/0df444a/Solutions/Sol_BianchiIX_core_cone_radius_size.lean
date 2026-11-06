-- Prove2me | solution 1 for BianchiIX.core_cone_radius_size
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:27:51.609217+00:00
-- url     : https://prove2.me/submissions/855babd7-7df6-48df-960e-510b2548852d

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


/-- The radial error vanishes with the actual wall sum, rather than just its fixed upper bound. -/
theorem solution {k ε u w a b : ℝ} (hk : 6 ≤ k)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w) :
    Real.sqrt u + (u + w) * (1 + k * |a| + |b|) ≤ 5 * Real.sqrt (u + w) := by
  let B := u + w
  have hε0 := hε.1
  have hk0 : 0 < k := by linarith only [hk]
  have hB0 : 0 ≤ B := add_nonneg hu.1 hw.1
  have hkB : k * B ≤ 2 * ε := by
    have H := (le_div_iff₀ hk0).mp hu.2
    have H' := (le_div_iff₀ hk0).mp hw.2
    dsimp [B]
    nlinarith only [H, H']
  have hB1 : B ≤ 1 := by nlinarith only [hkB, hε.2, hk, hB0]
  have hsB : B ≤ Real.sqrt B := by
    have H := Real.sq_sqrt hB0
    have H' : Real.sqrt B ≤ 1 := by simpa using Real.sqrt_le_sqrt hB1
    nlinarith only [H, H', Real.sqrt_nonneg B]
  have hsu : Real.sqrt u ≤ Real.sqrt B := Real.sqrt_le_sqrt (by dsimp [B]; linarith only [hw.1])
  have hsw : Real.sqrt w ≤ Real.sqrt B := Real.sqrt_le_sqrt (by dsimp [B]; linarith only [hu.1])
  have hQ : 1 + k * |a| + |b| ≤ 1 + k * Real.sqrt u + Real.sqrt w := by
    nlinarith only [mul_le_mul_of_nonneg_left ha hk0.le, hb]
  calc
    _ ≤ Real.sqrt B + B * (1 + k * Real.sqrt u + Real.sqrt w) :=
      add_le_add hsu (mul_le_mul_of_nonneg_left hQ hB0)
    _ = Real.sqrt B + B + (k * B) * Real.sqrt u + B * Real.sqrt w := by ring
    _ ≤ Real.sqrt B + Real.sqrt B + (2 * ε) * Real.sqrt B + 1 * Real.sqrt B := by
      gcongr
    _ ≤ 5 * Real.sqrt B := by
      nlinarith only [mul_le_mul_of_nonneg_right hε.2 (Real.sqrt_nonneg B)]
