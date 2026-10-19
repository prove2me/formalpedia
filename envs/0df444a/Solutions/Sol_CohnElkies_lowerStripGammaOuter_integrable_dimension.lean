-- Prove2me | solution 1 for CohnElkies.lowerStripGammaOuter_integrable_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/54e43cda-ea83-4ac7-a925-43a5970fbad4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerStripGammaOuter_integrable_of_exp_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_exp_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ} {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹'
      Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2) z y *
          (lowerGammaBoundaryLog ((d : ℝ) / 2) R y : ℂ)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  apply lowerStripGammaOuter_integrable_of_exp_integrable hℓ hz
  exact lowerGammaBoundaryLog_dimension_exp_integrable hd
    (div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)) R
end CohnElkies
