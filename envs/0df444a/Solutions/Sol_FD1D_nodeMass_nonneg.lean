-- Prove2me | solution 1 for FD1D.nodeMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:38.326244+00:00
-- url     : https://prove2.me/submissions/ee912182-6fc5-4735-a473-93bbae92c4f9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_nodeMass_pos

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (d : ℕ) (v : DyadicNode d) :
    0 ≤ nodeMass d v :=
  (nodeMass_pos d v).le
end FD1D
