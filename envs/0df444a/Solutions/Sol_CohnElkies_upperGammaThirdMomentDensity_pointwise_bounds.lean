-- Prove2me | solution 1 for CohnElkies.upperGammaThirdMomentDensity_pointwise_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/bafee6a5-60eb-40be-9ec2-0909b5277501

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds

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
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * a * Real.exp (-η * a) ≤
      a ^ 3 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 3 * upperGammaMeasureDensity ℓ η a ≤
      (a ^ 2 + (ℓ / 2) * a) *
        Real.exp (-η * a) := by
  obtain ⟨hlower, hupper⟩ :=
    upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha
  have hlow := mul_le_mul_of_nonneg_left hlower ha.le
  have hupp := mul_le_mul_of_nonneg_left hupper ha.le
  constructor <;> nlinarith
end CohnElkies
