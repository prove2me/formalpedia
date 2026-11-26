-- Prove2me | solution 1 for EdenVerified.p02_radialField_pos_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:56.153215+00:00
-- url     : https://prove2.me/submissions/42a7f160-161d-4472-a2f5-4cbe04df63d8

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialField_pos_between


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < Real.sqrt 2),
    radialField r > 0 :=
  @Eden.radialField_pos_between
end EdenVerified
