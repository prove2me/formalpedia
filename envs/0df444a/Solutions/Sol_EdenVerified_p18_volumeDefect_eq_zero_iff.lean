-- Prove2me | solution 1 for EdenVerified.p18_volumeDefect_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:28:30.032863+00:00
-- url     : https://prove2.me/submissions/4ebb9de9-1a85-474b-90fb-58972f565637

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_volumeDefect_eq_zero_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    volumeDefect t p = 0 ↔ p ∈ torus :=
  @Eden.volumeDefect_eq_zero_iff
end EdenVerified
