-- Prove2me | solution 1 for FD1D.AggregatedInventory.leaf_count_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:08.370149+00:00
-- url     : https://prove2.me/submissions/69b31d9e-26f2-4d9e-8f08-bd8d46dd48b8

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_AggregatedInventory_level_count_eq

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
namespace AggregatedInventory
theorem _root_.solution
    {L m : ℕ} (I : AggregatedInventory L m) :
    ∑ v, I.count L v = m :=
  I.level_count_eq le_rfl
end AggregatedInventory
end FD1D
