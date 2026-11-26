-- Prove2me | solution 1 for FourierJacobi.Analysis.i0RegionIndex_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:47.998847+00:00
-- url     : https://prove2.me/submissions/fc84eb12-524b-486b-b4f4-85cc97aa1498

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : p ∈ i0Region (i0RegionIndex p) := by
  unfold i0RegionIndex
  split_ifs <;> norm_num [i0Region] <;> omega
end FourierJacobi.Analysis
