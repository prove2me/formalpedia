-- Prove2me | solution 1 for AvramDividend.Classical.exists_countable_dense_nnreal_time_set_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:30:42.167513+00:00
-- url     : https://prove2.me/submissions/7dc5da3e-38c2-417a-b53d-95df9c89c626

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Bases
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.BoundedOrder.Basic
open AvramDividend.Classical Set Topology
open scoped NNReal
theorem solution :
    ∃ S : Set ℝ≥0,
      S.Countable ∧ Dense S ∧ (0 : ℝ≥0) ∈ S := by
  obtain ⟨T, hT, hd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  exact ⟨insert 0 T, hT.insert 0, hd.mono (subset_insert _ _), mem_insert _ _⟩
