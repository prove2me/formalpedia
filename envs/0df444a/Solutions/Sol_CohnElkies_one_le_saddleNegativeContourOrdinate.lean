-- Prove2me | solution 1 for CohnElkies.one_le_saddleNegativeContourOrdinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/db056d5c-6c13-44c6-8876-19b703a5cf0b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    1 ≤ saddleNegativeContourOrdinate ℓ N := by
  unfold saddleNegativeContourOrdinate
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hq : 0 ≤ (2 * (N : ℝ) + 1) / ℓ := by positivity
  linarith
end CohnElkies
