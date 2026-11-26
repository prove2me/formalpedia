-- Prove2me | solution 1 for EdenVerified.p24_asymptoticDimension_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:16:38.657987+00:00
-- url     : https://prove2.me/submissions/99707469-985c-43ee-8952-a9c934c92aba

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_at_origin


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    asymptoticDimension c 0 = 0 :=
  @Eden.asymptoticDimension_at_origin
end EdenVerified
