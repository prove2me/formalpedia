-- Prove2me | solution 1 for Eden.strictMono_squaredRadiusEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:50.50375+00:00
-- url     : https://prove2.me/submissions/f25d03dc-36d0-44eb-b9a7-95218efb0f22

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_parameter
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) :
    StrictMono (squaredRadiusEvolution t) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_squaredRadiusEvolution_parameter ht)
  intro s
  exact div_pos (Real.exp_pos _) (pow_pos (sqrt_radialDiscriminant_pos ht s) _)
end Eden
