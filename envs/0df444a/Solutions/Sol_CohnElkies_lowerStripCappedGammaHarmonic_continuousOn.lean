-- Prove2me | solution 1 for CohnElkies.lowerStripCappedGammaHarmonic_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/fb92077d-a4f2-4377-9234-4d7364dc15f7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_differentiableOn_dimension
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_bottom_re_joint_tendsto
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_top_re_joint_tendsto
import Theorems.Thm_CohnElkies_horizontalStripRealTraceExtension_continuousOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ContinuousOn (lowerStripCappedGammaHarmonic d R D)
      (Complex.im ⁻¹'
        Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  unfold lowerStripCappedGammaHarmonic
  apply horizontalStripRealTraceExtension_continuousOn
    (show -((d : ℝ) / 2) < (d : ℝ) / 2 by linarith)
  · exact Complex.continuous_re.comp_continuousOn
      (lowerStripCappedGammaOuter_differentiableOn_dimension
        hd R D).continuousOn
  · exact lowerGammaBoundaryCapped_continuous hℓ R D
  · fun_prop
  · intro s
    simpa [sub_eq_add_neg] using!
      lowerStripCappedGammaOuter_bottom_re_joint_tendsto
        hd R D s
  · intro s
    simpa using!
      lowerStripCappedGammaOuter_top_re_joint_tendsto
        hd R D s
end CohnElkies
