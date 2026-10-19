-- Prove2me | solution 1 for CohnElkies.plusSaddleProfile_div_origin_eq_small_radius_residue_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/101914d0-f4bf-42fd-bab9-4b67de0c7aed

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddleProfile_eq_small_radius_residue_series

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
    plusSaddleProfile ε ℓ r /
        (saddleOriginValue ε ℓ : ℂ) =
      ((∑ n ∈ Finset.range (N + 1),
        (-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ) *
            plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ) := by
  have hzero : (saddleOriginValue ε ℓ : ℂ) ≠ 0 := by
    exact_mod_cast (saddleOriginValue_pos hε ℓ).ne'
  rw [plusSaddleProfile_eq_small_radius_residue_series
    hε hℓ horder hr N]
  field_simp [hzero]
end CohnElkies
