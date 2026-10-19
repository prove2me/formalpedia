-- Prove2me | solution 1 for CohnElkies.radialProfile_locallyIntegrableOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/ff300fc9-54e9-4808-a954-2f5f3aec7c64

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    LocallyIntegrableOn
      (radialProfile hd f) (Ioi (0 : ℝ)) :=
  (radialProfile_continuous hd f).locallyIntegrable.locallyIntegrableOn _
end CohnElkies
