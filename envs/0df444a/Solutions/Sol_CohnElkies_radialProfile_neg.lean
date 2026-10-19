-- Prove2me | solution 1 for CohnElkies.radialProfile_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/4812bf8e-0df3-4316-8218-550467fcec95

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (r : ℝ) :
    radialProfile hd f (-r) = radialProfile hd f r := by
  unfold radialProfile
  apply hf
  simp [norm_smul, norm_radialUnitDirection hd]
end CohnElkies
