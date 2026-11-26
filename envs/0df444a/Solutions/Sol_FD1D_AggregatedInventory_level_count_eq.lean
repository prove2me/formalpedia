-- Prove2me | solution 1 for FD1D.AggregatedInventory.level_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:12.399028+00:00
-- url     : https://prove2.me/submissions/6888de27-cb7a-4344-b639-4677a4d20ee7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_CoherentTreeLabel_levelSum_eq_root

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
namespace AggregatedInventory
theorem _root_.solution
    {L m : ℕ} (I : AggregatedInventory L m) {d : ℕ} (hdL : d ≤ L) :
    ∑ v, I.count d v = m := by
  let f : CoherentTreeLabel L ℕ :=
    { value := I.count
      children := I.count_children }
  rw [show (∑ v, I.count d v) = levelSum f.value d by rfl]
  rw [f.levelSum_eq_root hdL]
  exact I.count_root
end AggregatedInventory
end FD1D
