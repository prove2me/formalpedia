-- Prove2me | solution 1 for EdenVerified.p26_geometricPeriodicOrbits_encard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:45.001836+00:00
-- url     : https://prove2.me/submissions/36e15f34-76ea-49ae-87b5-4f89b9c4b068

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_geometricPeriodicOrbits_encard


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 0 < c),
    (geometricPeriodicOrbits c).encard = 4 :=
  @Eden.geometricPeriodicOrbits_encard
end EdenVerified
