-- Prove2me | solution 1 for EdenVerified.p26_first_plane_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:18:46.40913+00:00
-- url     : https://prove2.me/submissions/dbb32613-f997-400c-9b48-73842fcb47f6

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_first_plane_return


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0) (hw : p 4 = 0),
    evolution c (2 * Real.pi) p = p :=
  @Eden.first_plane_return
end EdenVerified
