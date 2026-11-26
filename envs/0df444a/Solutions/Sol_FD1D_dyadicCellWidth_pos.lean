-- Prove2me | solution 1 for FD1D.dyadicCellWidth_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:37:50.288681+00:00
-- url     : https://prove2.me/submissions/169117cf-b01e-43a2-8db7-541fba341c93

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
namespace FD1D
theorem _root_.solution (L : ℕ) :
    0 < dyadicCellWidth L := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.two_pow_pos L
end FD1D
