-- Prove2me | solution 1 for EdenVerified.p06_radial_excess_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:34.928998+00:00
-- url     : https://prove2.me/submissions/23541e9b-7c26-4140-bc65-62a5721a85fb

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radial_excess_le


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M),
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 :=
  @Eden.radial_excess_le
end EdenVerified
