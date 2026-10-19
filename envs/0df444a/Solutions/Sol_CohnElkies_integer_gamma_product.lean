-- Prove2me | solution 1 for CohnElkies.integer_gamma_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/407c46fa-1413-4a78-91bf-b7a5777ea265

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CohnElkies
theorem _root_.solution (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    Complex.Gamma ((k : ℂ) + Complex.I * (y : ℂ) / 2) =
      Complex.Gamma (Complex.I * (y : ℂ) / 2) *
        ∏ j ∈ Finset.range k,
          ((j : ℂ) + Complex.I * (y : ℂ) / 2) := by
  let z : ℂ := Complex.I * (y : ℂ) / 2
  have hz : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hj
    have him := congrArg Complex.im hj
    try dsimp [z] at him
    norm_num at him
    exact hy (by linarith)
  simpa [z, add_comm] using! gamma_add_nat_eq_product z hz k
end CohnElkies
