-- Prove2me | solution 1 for FirstPassageLinearTransport.reciprocal_finite_multiplicative_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:52.72862+00:00
-- url     : https://prove2.me/submissions/1a9ade81-56d9-4ff1-b4ed-66981a986edf

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_normalized_multiplicativeHitCount_le_inv
import Theorems.Thm_FirstPassageLinearTransport_normalized_multiplicativeHitCount_ge
import Theorems.Thm_FirstPassageLinearTransport_reciprocalMaximumEpsilon_pos
import Theorems.Thm_FirstPassageLinearTransport_support_le_reciprocalMaximumSlope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (r : ℝ)) ≤
      (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r ∧
    (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r ≤ u⁻¹ := by
  have hlower := normalized_multiplicativeHitCount_ge hu hr
    (fun v hv ↦ support_le_reciprocalMaximumSlope hu hlog v hv)
    reciprocalMaximumEpsilon_pos
  have hconstant :
      3 / (16 * reciprocalMaximumEpsilon ^ 2 * (r : ℝ)) =
        reciprocalMaximumConstant / (r : ℝ) := by
    unfold reciprocalMaximumConstant
    ring
  rw [hconstant] at hlower
  exact ⟨hlower, normalized_multiplicativeHitCount_le_inv
    (zero_lt_one.trans_le hu) r⟩
end FirstPassageLinearTransport
