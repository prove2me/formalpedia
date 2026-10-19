-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusStarOrdinate_sourceScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/d051b2ed-fd3b-40af-8443-3652563c7826

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (ε : ℝ)
    {u : ℝ}
    (hu : saddleSmallRadiusStarOrdinate ε d ≤ u) :
    Real.log ((d : ℝ) / 2) / 4 ≤
      ((d : ℝ) / 2) * (1 + u) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ := by
    try dsimp [ℓ]
    positivity
  have hstar :
      ℓ * (1 + saddleSmallRadiusStarOrdinate ε d) =
        Real.log ℓ / 4 := by
    unfold saddleSmallRadiusStarOrdinate
    try dsimp [ℓ]
    field_simp [hℓ.ne']
    ring
  change Real.log ℓ / 4 ≤ ℓ * (1 + u)
  rw [← hstar]
  apply mul_le_mul_of_nonneg_left _ hℓ.le
  linarith
end CohnElkies
