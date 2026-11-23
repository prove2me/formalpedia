-- Prove2me | solution 1 for Formalism.DimensionVariation.sharp_cost
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:16.678329+00:00
-- url     : https://prove2.me/submissions/cfdd5655-30b2-4198-a332-2c8593ec007a

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : SharpCost := by
  intro n n' g f N hn hn' hg hf hN h1 h2
  have hg0 : 0 < g := lt_of_lt_of_le one_pos hg
  have hlg : 0 ≤ Real.log g := Real.log_nonneg hg
  have hNN : f * N * Real.log g ≤ f * N ^ 2 * Real.log g := by
    have : N ≤ N ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hf) hlg
  have one : ∀ k : ℕ, 1 ≤ k → ((k : ℝ) ≤ g ^ (f * N ^ 2) ∨ (k : ℝ) ≤ g ^ (f * N)) →
      Real.log k ≤ f * N ^ 2 * Real.log g := by
    intro k hk hk'
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    rcases hk' with hk' | hk'
    · calc Real.log k ≤ Real.log (g ^ (f * N ^ 2)) := Real.log_le_log hk0 hk'
        _ = f * N ^ 2 * Real.log g := Real.log_rpow hg0 _
    · calc Real.log k ≤ Real.log (g ^ (f * N)) := Real.log_le_log hk0 hk'
        _ = f * N * Real.log g := Real.log_rpow hg0 _
        _ ≤ f * N ^ 2 * Real.log g := hNN
  have a1 := one n hn h1
  have a2 := one n' hn' h2
  refine ⟨a1, a2, ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn0' : (0 : ℝ) < n' := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul hn0.ne' hn0'.ne']
  linarith
end Formalism.DimensionVariation
