-- Prove2me | solution 1 for Eden.contDiffAt_planarAmplitude_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:24.99468+00:00
-- url     : https://prove2.me/submissions/930a0a95-c689-46d1-9afb-57d157d226e5

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
import Theorems.Thm_Eden_contDiffAt_amplitudeSq_joint
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × ℝ => planarAmplitude u.1 u.2) (t, s) :=
  (contDiffAt_amplitudeSq_joint (radialDiscriminant_pos ht s) n).sqrt
    (amplitudeSq_pos ht hs).ne'
end Eden
