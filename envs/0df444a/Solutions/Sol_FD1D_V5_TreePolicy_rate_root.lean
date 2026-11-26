-- Prove2me | solution 1 for FD1D.V5.TreePolicy.rate_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:35:20.648049+00:00
-- url     : https://prove2.me/submissions/f7d74a47-de0e-4f67-81f0-d94288bcbeb4

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m) (a : ℝ) :
    rate I a 0 dyadicRoot = 1 / (m : ℝ) :=
  rfl
end FD1D.V5.TreePolicy
