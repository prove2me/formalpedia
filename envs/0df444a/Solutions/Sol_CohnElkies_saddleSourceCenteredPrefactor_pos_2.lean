-- Prove2me | solution 2 for CohnElkies.saddleSourceCenteredPrefactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:04.269967+00:00
-- url     : https://prove2.me/submissions/261804b8-6d48-4fbe-a736-e41800e19b82

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology


theorem solution
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (v : ℝ) :
    0 < saddleSourceCenteredPrefactor ε ℓ u v := by
  unfold saddleSourceCenteredPrefactor saddleSourceContourEnvelopeScale
  have hg : 0 < Real.Gamma (ℓ * (1 + u) / 2) :=
    Real.Gamma_pos_of_pos (by have : 0 < 1 + u := by linarith
                              positivity)
  have := Real.pi_pos
  positivity

