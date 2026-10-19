-- Prove2me | solution 1 for CohnElkies.plusSaddleRegularMellinFactor_neg_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/e8a751f6-9db3-4fe3-9f60-73f5235aa256

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleMellinShellArgument_neg_even
import Theorems.Thm_CohnElkies_saddleRegularMellinFactor_neg_even

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddleRegularMellinFactor ε ℓ
        (-((2 * n : ℕ) : ℂ)) =
      ((Real.pi ^ (ℓ / 2 + (n : ℝ)) *
        Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) *
        plusPolynomial ε
          (Complex.I *
            ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ)) := by
  unfold plusSaddleRegularMellinFactor
  rw [saddleRegularMellinFactor_neg_even hℓ n,
    saddleMellinShellArgument_neg_even hℓ n]
end CohnElkies
