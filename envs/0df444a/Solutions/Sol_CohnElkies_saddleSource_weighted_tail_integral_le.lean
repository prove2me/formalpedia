-- Prove2me | solution 1 for CohnElkies.saddleSource_weighted_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/4197d54d-3c61-435e-b25a-97d4441891a5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussianTailSet_measurable

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
    {F : ℝ → ℂ} {W : ℝ → ℝ} {C A R : ℝ}
    (hF : Integrable F)
    (hW : Integrable W)
    (hpoint : ∀ T ∈ saddleGaussianTailSet R,
      ‖F T‖ ≤ (C * A) * W T) :
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤
      C * A * (∫ T : ℝ in saddleGaussianTailSet R, W T) := by
  have hmajor : Integrable (fun T : ℝ => (C * A) * W T) :=
    hW.const_mul (C * A)
  have hcompare := setIntegral_mono_on
    hF.norm.integrableOn hmajor.integrableOn
      (saddleGaussianTailSet_measurable R) hpoint
  calc
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        (C * A) * W T := hcompare
    _ = C * A *
        (∫ T : ℝ in saddleGaussianTailSet R, W T) := by
      rw [integral_const_mul]
end CohnElkies
