-- Prove2me | solution 1 for CohnElkies.saddleMellinShellArgument_neg_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/0b0492f5-0645-4563-9a82-4d5e2767587b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {ℓ : ℝ}
    (hℓ : 0 < ℓ) (n : ℕ) :
    Complex.I *
        ((-((2 * n : ℕ) : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ) =
      Complex.I *
        ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ) := by
  have hc : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  push_cast
  field_simp [hc]; ring
end CohnElkies
