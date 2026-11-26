-- Prove2me | solution 1 for Eden.multiset_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:22.686103+00:00
-- url     : https://prove2.me/submissions/e1e34dd1-a289-4327-b87a-1f1401937a3e

import Definitions.Def_Eden_OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_Eden_Sorting
import Theorems.Thm_Eden_ofFn_descending

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} (f : Fin n → ℝ) :
    Finset.univ.val.map (descending f) = Finset.univ.val.map f := by
  rw [Fin.univ_val_map, ofFn_descending, Multiset.sort_eq]
end Eden
