-- Prove2me | solution 1 for Eden.continuous_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:11:12.092004+00:00
-- url     : https://prove2.me/submissions/aaebc0e5-7e10-4ddb-837b-2e432e16a357

import Definitions.Def_Eden_OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_Eden_Sorting
import Theorems.Thm_Eden_lipschitzWith_descending

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (n : ℕ) :
    Continuous (descending : (Fin n → ℝ) → (Fin n → ℝ)) :=
  (lipschitzWith_descending n).continuous
end Eden
