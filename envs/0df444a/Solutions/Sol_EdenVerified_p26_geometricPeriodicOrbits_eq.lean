-- Prove2me | solution 1 for EdenVerified.p26_geometricPeriodicOrbits_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:33.221242+00:00
-- url     : https://prove2.me/submissions/79fd1c7c-87fe-40da-bcf1-79a57735beff

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_geometricPeriodicOrbits_eq


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 0 < c),
    geometricPeriodicOrbits c = {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} :=
  @Eden.geometricPeriodicOrbits_eq
end EdenVerified
