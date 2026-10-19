-- Prove2me | solution 1 for CohnElkies.radialProfile_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/6a58ac07-adb7-4495-9911-98849ed1fa7a

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
    (f : TestFunction d) (hf : IsRealValued f) (r : ℝ) :
    (radialProfile hd f r).im = 0 :=
  hf (r • radialUnitDirection hd)
end CohnElkies
