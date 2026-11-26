-- Prove2me | solution 1 for EdenVerified.p25_not_simultaneous_rotation_returns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:18.273526+00:00
-- url     : https://prove2.me/submissions/35b52865-ee62-4150-bae9-4086a4f8048e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_not_simultaneous_rotation_returns


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t : ℝ} (ht : 0 < t),
    ¬(Real.cos t = 1 ∧ Real.cos (Real.sqrt 2 * t) = 1) :=
  @Eden.not_simultaneous_rotation_returns
end EdenVerified
