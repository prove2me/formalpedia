-- Prove2me | solution 1 for EdenVerified.p26_second_plane_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:18:55.502877+00:00
-- url     : https://prove2.me/submissions/c2508be4-dd38-4e04-8d98-fd503d45a65e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_second_plane_return


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 0) (h₂ : radiusSq₂ p = 1 ∨ radiusSq₂ p = 2)
    (hw : p 4 = 0),
    evolution c (2 * Real.pi / Real.sqrt 2) p = p :=
  @Eden.second_plane_return
end EdenVerified
