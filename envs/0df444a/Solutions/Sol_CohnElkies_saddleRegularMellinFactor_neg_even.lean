-- Prove2me | solution 1 for CohnElkies.saddleRegularMellinFactor_neg_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/0f50472a-4a9b-445c-975b-3208bed5183e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_neg
import Theorems.Thm_CohnElkies_saddleMellinShellArgument_neg_even

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
    saddleRegularMellinFactor ε ℓ (-((2 * n : ℕ) : ℂ)) =
      ((Real.pi ^ (ℓ / 2 + (n : ℝ)) *
        Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) := by
  have hpi :
      Complex.exp
        (((ℓ : ℂ) - (-((2 * n : ℕ) : ℂ))) *
          (Real.log Real.pi : ℂ) / 2) =
        ((Real.pi ^ (ℓ / 2 + (n : ℝ)) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase :
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          (Complex.I *
            ((-((2 * n : ℕ) : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ))) =
        (Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ)) : ℂ) := by
    rw [saddleMellinShellArgument_neg_even hℓ n,
      mellinShellPhase_imaginary,
      realHyperbolicShellPhase_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold saddleRegularMellinFactor
  rw [hpi, hphase, ← Complex.ofReal_mul]
end CohnElkies
