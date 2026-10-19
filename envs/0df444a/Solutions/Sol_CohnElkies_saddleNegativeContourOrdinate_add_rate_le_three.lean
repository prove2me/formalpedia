-- Prove2me | solution 1 for CohnElkies.saddleNegativeContourOrdinate_add_rate_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/b5607056-0b41-4f00-b543-67f6a4980344

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
    saddleNegativeContourOrdinate ℓ N +
        saddleNegativeGammaRate ℓ N ≤ 3 := by
  unfold saddleNegativeContourOrdinate saddleNegativeGammaRate
  have hratio : (4 * (N : ℝ) + 4) / ℓ ≤ 2 := by
    apply (div_le_iff₀ hℓ).2
    norm_num [Nat.cast_add, Nat.cast_one] at hN
    nlinarith
  calc
    1 + (2 * (N : ℝ) + 1) / ℓ +
        (2 * (N : ℝ) + 3) / ℓ =
      1 + (4 * (N : ℝ) + 4) / ℓ := by ring
    _ ≤ 1 + 2 := by
      simpa [add_comm] using! add_le_add_left hratio 1
    _ = 3 := by norm_num
end CohnElkies
