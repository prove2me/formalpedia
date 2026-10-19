-- Prove2me | solution 1 for CohnElkies.lowerStripCappedGammaOuter_differentiableOn_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/1c648d56-2b35-4ec4-a998-c08bdef5aa79

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous
import Theorems.Thm_CohnElkies_stripRegularizedOuter_differentiableAt_of_exp_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_exp_integrable_dimension

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    DifferentiableOn ℂ
      (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have ha : 0 < Real.pi / (2 * ((d : ℝ) / 2)) :=
    div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  intro z hz
  unfold lowerStripCappedGammaOuter
  exact (stripRegularizedOuter_differentiableAt_of_exp_integrable
    hℓ hz
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (lowerGammaBoundaryCapped_continuous hℓ R D)
    (lowerGammaBoundaryCapped_exp_integrable_dimension
      hd ha R D)).differentiableWithinAt
end CohnElkies
