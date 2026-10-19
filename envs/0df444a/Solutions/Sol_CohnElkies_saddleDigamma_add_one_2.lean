-- Prove2me | solution 2 for CohnElkies.saddleDigamma_add_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:32.317283+00:00
-- url     : https://prove2.me/submissions/4417025f-b296-446a-9d51-e9b1ef3ac354

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {m : ℝ} (hm : 0 < m) :
    saddleDigamma (m + 1) =
      saddleDigamma m + m⁻¹ := by
  have hev : (fun x => (Real.log ∘ Real.Gamma) (x + 1)) =ᶠ[nhds m]
      fun x => (Real.log ∘ Real.Gamma) x + Real.log x := by
    filter_upwards [lt_mem_nhds hm] with x hx
    exact saddleLogGamma_add_one hx
  have h1 : deriv (fun x => (Real.log ∘ Real.Gamma) (x + 1)) m = saddleDigamma (m + 1) := by
    rw [deriv_comp_add_const]; rfl
  rw [← h1, hev.deriv_eq]
  exact ((saddleLogGamma_differentiableAt hm).hasDerivAt.add (Real.hasDerivAt_log hm.ne')).deriv

