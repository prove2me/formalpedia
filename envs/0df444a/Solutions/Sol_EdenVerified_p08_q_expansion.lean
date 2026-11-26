-- Prove2me | solution 1 for EdenVerified.p08_q_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:27.846805+00:00
-- url     : https://prove2.me/submissions/f596c14f-0eb0-4d14-9561-96424cd6b290

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_q_expansion


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    q s = -s ^ 2 + 3 * s - 2 :=
  @Eden.q_expansion
end EdenVerified
