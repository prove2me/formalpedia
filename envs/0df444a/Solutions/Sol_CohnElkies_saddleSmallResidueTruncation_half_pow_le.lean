-- Prove2me | solution 1 for CohnElkies.saddleSmallResidueTruncation_half_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/2a1d20a7-e66b-41ad-abc0-38ed075c6326

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallResidueTruncation_lower
import Theorems.Thm_CohnElkies_saddleSmallResidue_half_log_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (ℓ : ℝ) :
    (1 / 2 : ℝ) ^
        (saddleSmallResidueTruncation ℓ + 1) ≤
      Real.exp (-10 * Real.log ℓ) := by
  let m : ℕ := saddleSmallResidueTruncation ℓ + 1
  have hmlower :
      20 * Real.log ℓ ≤ (m : ℝ) := by
    try dsimp [m]
    push_cast
    linarith [saddleSmallResidueTruncation_lower ℓ]
  have hhalf := saddleSmallResidue_half_log_le
  have hproduct :=
    mul_le_mul_of_nonneg_left hhalf
      (show 0 ≤ (m : ℝ) by positivity)
  have hexponent :
      (m : ℝ) * Real.log (1 / 2 : ℝ) ≤
        -10 * Real.log ℓ := by
    nlinarith
  change (1 / 2 : ℝ) ^ m ≤ _
  calc
    (1 / 2 : ℝ) ^ m =
        Real.exp ((m : ℝ) * Real.log (1 / 2 : ℝ)) := by
      rw [Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ Real.exp (-10 * Real.log ℓ) :=
      Real.exp_le_exp.mpr hexponent
end CohnElkies
