-- Prove2me | solution 1 for EdenVerified.p17_volumeDefect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:43.815959+00:00
-- url     : https://prove2.me/submissions/b9cf1af7-6ff1-49e6-b13c-b1b1590d3a3e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_volumeDefect_nonneg


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    0 ≤ volumeDefect t p :=
  @Eden.volumeDefect_nonneg
end EdenVerified
