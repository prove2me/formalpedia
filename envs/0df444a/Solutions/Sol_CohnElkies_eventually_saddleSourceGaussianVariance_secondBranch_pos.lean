-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceGaussianVariance_secondBranch_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/d42be968-df05-4b48-9c2f-a1b5eea5b406

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upperSaddleVariance_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          0 < saddleSourceGaussianVariance ε ℓ (1 + δ) := by
  filter_upwards [eventually_upperSaddleVariance_pos]
    with ε hpositive
  intro ℓ hℓ δ hδ
  convert! hpositive ℓ hℓ δ hδ using 1
  all_goals simp [saddleSourceGaussianVariance]
end CohnElkies
