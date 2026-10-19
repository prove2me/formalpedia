-- Prove2me | solution 1 for CohnElkies.saddleNegativeContourOrdinate_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/cb470c9d-57a6-407b-b9d0-7270656d9b30

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ) :
    saddleNegativeContourOrdinate ℓ N ≤ 2 := by
  unfold saddleNegativeContourOrdinate
  have hratio : (2 * (N : ℝ) + 1) / ℓ ≤ 1 := by
    apply (div_le_iff₀ hℓ).2
    norm_num [Nat.cast_add, Nat.cast_one] at hN
    nlinarith
  linarith
end CohnElkies
