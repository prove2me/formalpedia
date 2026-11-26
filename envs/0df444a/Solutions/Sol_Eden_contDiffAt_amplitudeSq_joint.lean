-- Prove2me | solution 1 for Eden.contDiffAt_amplitudeSq_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:36.4535+00:00
-- url     : https://prove2.me/submissions/95f193b8-f7ac-4b30-a0c8-81512d3e1919

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (hD : 0 < radialDiscriminant t s)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × ℝ => amplitudeSq u.1 u.2) (t, s) := by
  have hd : ContDiffAt ℝ n (fun u : ℝ × ℝ => radialDiscriminant u.1 u.2) (t, s) := by
    unfold radialDiscriminant
    fun_prop
  have hr := hd.sqrt (ne_of_gt hD)
  have hR : Real.sqrt (radialDiscriminant t s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hR1 : Real.sqrt (radialDiscriminant t s) + 1 ≠ 0 := by positivity
  unfold amplitudeSq
  apply ContDiffAt.div _ hr hR
  apply ContDiffAt.add contDiffAt_const
  apply ContDiffAt.div _ (hr.add contDiffAt_const) hR1
  fun_prop
end Eden
