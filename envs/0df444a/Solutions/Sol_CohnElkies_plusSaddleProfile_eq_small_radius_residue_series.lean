-- Prove2me | solution 1 for CohnElkies.plusSaddleProfile_eq_small_radius_residue_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/886220dc-f06b-438f-80a5-b0c53f438a7c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddlePoleResidue_mul_pow_eq_smallCoefficient

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
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r =
      (saddleOriginValue ε ℓ : ℂ) *
        ((∑ n ∈ Finset.range (N + 1),
          (-saddleSmallRadiusVariable ε r) ^ n /
            (n.factorial : ℝ) *
              plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r := by
  rw [plusSaddleProfile_eq_residue_sum_add_remainder
    hε hℓ horder hr N]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hterm :=
    plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
      hε hℓ n r
  push_cast at hterm
  simpa only [mul_assoc] using! hterm
end CohnElkies
