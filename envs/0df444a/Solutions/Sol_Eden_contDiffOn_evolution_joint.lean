-- Prove2me | solution 1 for Eden.contDiffOn_evolution_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:36.11278+00:00
-- url     : https://prove2.me/submissions/fceb63c7-1a21-46c3-93bc-b6a30cf0470c

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
import Theorems.Thm_Eden_contDiffAt_evolution_joint

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun u : ℝ × PhaseSpace => evolution c u.1 u.2)
      {u | 0 ≤ u.1} := by
  intro u hu
  exact (contDiffAt_evolution_joint c hu u.2 n).contDiffWithinAt
end Eden
