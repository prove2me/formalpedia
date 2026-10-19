-- Prove2me | solution 1 for CohnElkies.plusSaddlePoleResidue_explicit_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/342a15e0-7266-49f8-901e-7bf2905a3368

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddleRegularMellinFactor_neg_even
import Theorems.Thm_CohnElkies_plusPolynomial_negative_imaginary_residue

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
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddlePoleResidue ε ℓ n =
      ((2 * (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        (Real.pi ^ (ℓ / 2 + (n : ℝ)) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (1 + 2 * (n : ℝ) / ℓ))) *
        (beta ε - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) : ℝ) : ℂ) := by
  unfold plusSaddlePoleResidue
  rw [plusSaddleRegularMellinFactor_neg_even hℓ n,
    plusPolynomial_negative_imaginary_residue]
  push_cast
  ring
end CohnElkies
